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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_apaA_b LibSegBa_apaB0_b LibSegBa_apaS0_b LibSegBa_apaS2_b LibSegBa_apaHX_b LibSegBa_apaH0_b LibSegBa_apaH1_b LibSegBa_apaH2_b LibSegBa_apaH3_b LibSegBa_apaH4_b LibSegBa_apaR_b LibSegBa_apaV_b LibSegBa_apaD1_b LibSegBa_apaD2_b LibSegBa_apaD3_b LibSegBa_apaD4e_b LibSegBa_apaD4z_b LibSegBa_apaD4n_b LibSegBa_apaDE_b LibSegBa_apaDZ_b LibSegBa_apaY1_b LibSegBa_apaY2_b LibSegBa_apaY3_b LibSegBa_apaY4e_b LibSegBa_apaY4z_b LibSegBa_apaY4n_b LibSegBa_apaYE_b LibSegBa_apaYZ_b LibSegBa_apaD5_b LibSegBa_apaY5_b LibSegBa_apaY6_b LibSegBa_apaC1_b LibSegBa_apaC2_b LibSegBa_apaJ0_b LibSegBa_apaJ4_b LibSegBa_apaT0_b LibSegBa_apaT1_b LibSegBa_apaX_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAPAP.
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
Module PapaA := LibSegBa_apaA_b.
Definition KS_apaA : list nat := Eval vm_compute in (BG.kept_list 80 PapaA.regs0 PapaA.regs_out0).
Lemma KS_apaA_ok : BG.kept_ok 80 PapaA.regs0 PapaA.regs_out0 KS_apaA = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 256) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 256) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xade6c M) (st fx' R' 0x5dda0 M')
        /\ (forall x, In x KS_apaA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 712420
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 256)
        /\ getr R' (reg 10) = Z_to_bv 64 128
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = getr R (reg 21)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 26) = getr R (reg 26)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 36%nat)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 256) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G10 G11 G12 K0 K1 K2 pvzI5 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PapaA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaA.kn0).
  { unfold know_ok, PapaA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 256) <= bv_unsigned a < (vz_2 - 256) + 256) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapaA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaA.ps0) with 0x5dda0 in Hms. change (SR.ps_regs PapaA.ps0) with (map (fun i => (i, nth i PapaA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaA.ps0) with PapaA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaA.regs0 PapaA.regs_out0 80 KS_apaA KS_apaA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PapaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PapaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PapaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PapaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PapaA.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PapaA.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PapaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaA.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PapaA.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PapaA.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PapaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaA.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PapaA.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV36l HV36r) | clear; lia]. }
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
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaB0 := LibSegBa_apaB0_b.
Definition KS_apaB0 : list nat := Eval vm_compute in (BG.kept_list 80 PapaB0.regs0 PapaB0.regs_out0).
Lemma KS_apaB0_ok : BG.kept_ok 80 PapaB0.regs0 PapaB0.regs_out0 KS_apaB0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaB0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 24) = Z_to_bv 64 (V 33%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 128 ->
  L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xadee4 M) (st fx' R' 0xadf94 M')
        /\ (forall x, In x KS_apaB0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 256)
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 12) = Z_to_bv 64 712300
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551602
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 15) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450890) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450889) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450895) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450894) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450893) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450892) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) 712300
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) 111258
        /\ L5.u64_at RSEGS M' (V 50%nat) 1102416563
        /\ L5.defined M' ((V 50%nat) + 24) 104).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G22 G24 pvzI6 K1 K2 pvzI7 K4 pvzI8 K6 K7 K8 K9 K10 K11 pvzI9 K13 K14 K15 K16 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV51l; move HV51l before pvzI5; pose proof (proj2 pvzI5) as HV51r; move HV51r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K5l; move K5l before pvzI8; pose proof (proj2 pvzI8) as K5r; move K5r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaB0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaB0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaB0.kn0).
  { unfold know_ok, PapaB0.kn0.
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
  pvz_hg ltac:(idtac; destruct (PapaB0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaB0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 24) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PapaB0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaB0.ps0) with 0xadf94 in Hms. change (SR.ps_regs PapaB0.ps0) with (map (fun i => (i, nth i PapaB0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaB0.ps0) with PapaB0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaB0.regs0 PapaB0.regs_out0 80 KS_apaB0 KS_apaB0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaB0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaB0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaB0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaB0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PapaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaB0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PapaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaB0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PapaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaB0.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PapaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaB0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PapaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaB0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PapaB0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaS0 := LibSegBa_apaS0_b.
Definition KS_apaS0 : list nat := Eval vm_compute in (BG.kept_list 80 PapaS0.regs0 PapaS0.regs_out0).
Lemma KS_apaS0_ok : BG.kept_ok 80 PapaS0.regs0 PapaS0.regs_out0 KS_apaS0 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma apaS0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 ((V 33%nat) + 256) -> getr R (reg 15) = Z_to_bv 64 (V 50%nat) -> getr R (reg 16) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 33%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> 6905856 <= (V 37%nat) <= 140737488355056 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 34 -> (((V 2%nat) - 256) + 256 <= (V 37%nat) \/ (V 37%nat) + 272 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 37%nat) \/ (V 37%nat) + 272 <= (V 33%nat)) ->
  ((V 50%nat) + 128 <= (V 37%nat) \/ (V 37%nat) + 272 <= (V 50%nat)) -> ((V 51%nat) + 1 <= (V 37%nat) \/ (V 37%nat) + 272 <= (V 51%nat)) -> L5.u64_at RSEGS M ((V 33%nat) + 256) (V 37%nat) -> L5.u64_at RSEGS M (V 37%nat) 1265968 ->
  L5KA.zeros_at M 2147609123 1 -> L5KA.zeros_at M ((((V 37%nat) + 152) / 8) + 2147450880) 1 -> ((((V 37%nat) / 8) + 2147450880) + 34 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 37%nat) / 8) + 2147450880)) -> L5.u8_at RSEGS M ((V 37%nat) + 152) 0 ->
  L5.u8_at RSEGS M ((V 33%nat) + 9) 0 -> 6905856 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 8 <= 2147446784) ->
  L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 256) + 256 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> ((V 50%nat) + 128 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 50%nat)) ->
  ((V 51%nat) + 1 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 51%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 8) -> ~ (((V 2%nat) - 184) <= bv_unsigned a < ((V 2%nat) - 184) + 8) -> ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 8) -> ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 8) -> ~ (((V 2%nat) - 168) <= bv_unsigned a < ((V 2%nat) - 168) + 8) -> ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 8) -> ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 8) -> ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 8) -> ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 8) -> ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 8) -> ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 8) -> ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 8) -> ~ (((V 2%nat) - 200) <= bv_unsigned a < ((V 2%nat) - 200) + 8) -> ~ (((V 2%nat) - 216) <= bv_unsigned a < ((V 2%nat) - 216) + 8) -> ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> ~ (((V 2%nat) - 184) <= i < ((V 2%nat) - 184) + 8) -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 8) -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 8) -> ~ (((V 2%nat) - 168) <= i < ((V 2%nat) - 168) + 8) -> ~ (((V 2%nat) - 232) <= i < ((V 2%nat) - 232) + 8) -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 8) -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 8) -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 8) -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 8) -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 8) -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 8) -> ~ (((V 2%nat) - 200) <= i < ((V 2%nat) - 200) + 8) -> ~ (((V 2%nat) - 216) <= i < ((V 2%nat) - 216) + 8) -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xadf94 M) (st fx' R' 0xae0cc M')
        /\ (forall x, In x KS_apaS0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 ((((V 33%nat) + 392) / 8) + 2147450880)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 34%nat) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 14) = getr R (reg 14)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 20) = Z_to_bv 64 40
        /\ getr R' (reg 21) = Z_to_bv 64 143316
        /\ getr R' (reg 22) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 33%nat) + 9)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 33%nat) + 400)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 50%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) ((V 50%nat) + 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G15 G16 G18 G22 G23 G24 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 K28 K29 pvzI11 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 pvzI12 K46 K47 K48 K49 K50 K51 K52.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K30l; move K30l before pvzI11; pose proof (proj2 pvzI11) as K30r; move K30r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K45l; move K45l before pvzI12; pose proof (proj2 pvzI12) as K45r; move K45r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 37%nat => Z_to_bv 64 vz_37 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 37%nat => vz_37 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaS0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaS0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaS0.kn0).
  { unfold know_ok, PapaS0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | exact (conj K30l K30r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | exactA K39]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K40]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | byte_tac ltac:(clear) | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | byte_tac ltac:(clear) | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | exact (conj K45l K45r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | clear; lia | exact K46]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52; lia | clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52; lia | clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaS0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaS0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 8) -> ~ ((vz_2 - 184) <= bv_unsigned a < (vz_2 - 184) + 8) -> ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 8) -> ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 8) -> ~ ((vz_2 - 168) <= bv_unsigned a < (vz_2 - 168) + 8) -> ~ ((vz_2 - 232) <= bv_unsigned a < (vz_2 - 232) + 8) -> ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 8) -> ~ ((vz_2 - 144) <= bv_unsigned a < (vz_2 - 144) + 8) -> ~ ((vz_2 - 136) <= bv_unsigned a < (vz_2 - 136) + 8) -> ~ ((vz_2 - 152) <= bv_unsigned a < (vz_2 - 152) + 8) -> ~ ((vz_2 - 176) <= bv_unsigned a < (vz_2 - 176) + 8) -> ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 8) -> ~ ((vz_2 - 200) <= bv_unsigned a < (vz_2 - 200) + 8) -> ~ ((vz_2 - 216) <= bv_unsigned a < (vz_2 - 216) + 8) -> ~ ((vz_2 - 256) <= bv_unsigned a < (vz_2 - 256) + 16) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8 Hn9 Hn10 Hn11 Hn12 Hn13 Hn14. apply Hfr. unfold PapaS0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn6; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn7; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn8; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn9; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn10; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn11; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn12; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn13; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn14; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8 Hn9 Hn10 Hn11 Hn12 Hn13 Hn14. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaS0.ps0) with 0xae0cc in Hms. change (SR.ps_regs PapaS0.ps0) with (map (fun i => (i, nth i PapaS0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaS0.ps0) with PapaS0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaS0.regs0 PapaS0.regs_out0 80 KS_apaS0 KS_apaS0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaS0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PapaS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PapaS0.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PapaS0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PapaS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS0.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PapaS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PapaS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PapaS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PapaS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PapaS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PapaS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS0.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PapaS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PapaS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS0.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PapaS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaS2 := LibSegBa_apaS2_b.
Definition KS_apaS2 : list nat := Eval vm_compute in (BG.kept_list 80 PapaS2.regs0 PapaS2.regs_out0).
Lemma KS_apaS2_ok : BG.kept_ok 80 PapaS2.regs0 PapaS2.regs_out0 KS_apaS2 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma apaS2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 ((V 33%nat) + 256) -> getr R (reg 15) = Z_to_bv 64 (V 50%nat) -> getr R (reg 16) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 33%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> 6905856 <= (V 37%nat) <= 140737488355056 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 34 -> (((V 2%nat) - 256) + 256 <= (V 37%nat) \/ (V 37%nat) + 272 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 37%nat) \/ (V 37%nat) + 272 <= (V 33%nat)) ->
  ((V 50%nat) + 128 <= (V 37%nat) \/ (V 37%nat) + 272 <= (V 50%nat)) -> ((V 51%nat) + 1 <= (V 37%nat) \/ (V 37%nat) + 272 <= (V 51%nat)) -> L5.u64_at RSEGS M ((V 33%nat) + 256) (V 37%nat) -> L5.u64_at RSEGS M (V 37%nat) 1265968 ->
  L5KA.zeros_at M 2147609123 1 -> L5KA.zeros_at M ((((V 37%nat) + 152) / 8) + 2147450880) 1 -> ((((V 37%nat) / 8) + 2147450880) + 34 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 37%nat) / 8) + 2147450880)) -> L5.u8_at RSEGS M ((V 37%nat) + 152) 2 ->
  L5.u8_at RSEGS M ((V 33%nat) + 9) 0 -> 6905856 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 8 <= 2147446784) ->
  L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 256) + 256 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> ((V 50%nat) + 128 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 50%nat)) ->
  ((V 51%nat) + 1 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 51%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 8) -> ~ (((V 2%nat) - 184) <= bv_unsigned a < ((V 2%nat) - 184) + 8) -> ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 8) -> ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 8) -> ~ (((V 2%nat) - 168) <= bv_unsigned a < ((V 2%nat) - 168) + 8) -> ~ (((V 2%nat) - 232) <= bv_unsigned a < ((V 2%nat) - 232) + 8) -> ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 8) -> ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 8) -> ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 8) -> ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 8) -> ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 8) -> ~ (((V 2%nat) - 208) <= bv_unsigned a < ((V 2%nat) - 208) + 8) -> ~ (((V 2%nat) - 200) <= bv_unsigned a < ((V 2%nat) - 200) + 8) -> ~ (((V 2%nat) - 216) <= bv_unsigned a < ((V 2%nat) - 216) + 8) -> ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> ~ (((V 2%nat) - 184) <= i < ((V 2%nat) - 184) + 8) -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 8) -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 8) -> ~ (((V 2%nat) - 168) <= i < ((V 2%nat) - 168) + 8) -> ~ (((V 2%nat) - 232) <= i < ((V 2%nat) - 232) + 8) -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 8) -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 8) -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 8) -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 8) -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 8) -> ~ (((V 2%nat) - 208) <= i < ((V 2%nat) - 208) + 8) -> ~ (((V 2%nat) - 200) <= i < ((V 2%nat) - 200) + 8) -> ~ (((V 2%nat) - 216) <= i < ((V 2%nat) - 216) + 8) -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xadf94 M) (st fx' R' 0xae0cc M')
        /\ (forall x, In x KS_apaS2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 ((((V 33%nat) + 392) / 8) + 2147450880)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 34%nat) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 14) = getr R (reg 14)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 20) = Z_to_bv 64 40
        /\ getr R' (reg 21) = Z_to_bv 64 143316
        /\ getr R' (reg 22) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 33%nat) + 9)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 33%nat) + 400)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 50%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) ((V 50%nat) + 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G15 G16 G18 G22 G23 G24 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 K28 K29 pvzI11 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 pvzI12 K46 K47 K48 K49 K50 K51 K52.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K30l; move K30l before pvzI11; pose proof (proj2 pvzI11) as K30r; move K30r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K45l; move K45l before pvzI12; pose proof (proj2 pvzI12) as K45r; move K45r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 37%nat => Z_to_bv 64 vz_37 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 37%nat => vz_37 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaS2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaS2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaS2.kn0).
  { unfold know_ok, PapaS2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | exact (conj K30l K30r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | exactA K39]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K40]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | clear - HV37l HV37r K30l K30r K32 K34 K35 K36 K37 K42; lia | byte_tac ltac:(clear) | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50; lia | byte_tac ltac:(clear) | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | exact (conj K45l K45r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | clear; lia | exact K46]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52; lia | clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52; lia | clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K52) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaS2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaS2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 8) -> ~ ((vz_2 - 184) <= bv_unsigned a < (vz_2 - 184) + 8) -> ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 8) -> ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 8) -> ~ ((vz_2 - 168) <= bv_unsigned a < (vz_2 - 168) + 8) -> ~ ((vz_2 - 232) <= bv_unsigned a < (vz_2 - 232) + 8) -> ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 8) -> ~ ((vz_2 - 144) <= bv_unsigned a < (vz_2 - 144) + 8) -> ~ ((vz_2 - 136) <= bv_unsigned a < (vz_2 - 136) + 8) -> ~ ((vz_2 - 152) <= bv_unsigned a < (vz_2 - 152) + 8) -> ~ ((vz_2 - 176) <= bv_unsigned a < (vz_2 - 176) + 8) -> ~ ((vz_2 - 208) <= bv_unsigned a < (vz_2 - 208) + 8) -> ~ ((vz_2 - 200) <= bv_unsigned a < (vz_2 - 200) + 8) -> ~ ((vz_2 - 216) <= bv_unsigned a < (vz_2 - 216) + 8) -> ~ ((vz_2 - 256) <= bv_unsigned a < (vz_2 - 256) + 16) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8 Hn9 Hn10 Hn11 Hn12 Hn13 Hn14. apply Hfr. unfold PapaS2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn6; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn7; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn8; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn9; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn10; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn11; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn12; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn13; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49 Hn14; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8 Hn9 Hn10 Hn11 Hn12 Hn13 Hn14. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaS2.ps0) with 0xae0cc in Hms. change (SR.ps_regs PapaS2.ps0) with (map (fun i => (i, nth i PapaS2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaS2.ps0) with PapaS2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaS2.regs0 PapaS2.regs_out0 80 KS_apaS2 KS_apaS2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaS2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PapaS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PapaS2.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PapaS2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PapaS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS2.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PapaS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PapaS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PapaS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PapaS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PapaS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PapaS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS2.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PapaS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS2.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PapaS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaS2.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PapaS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K45l K45r K47 K49 K50 K51 K52) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K50) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K49) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K42 K51) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaHX := LibSegBa_apaHX_b.
Definition KS_apaHX : list nat := Eval vm_compute in (BG.kept_list 80 PapaHX.regs0 PapaHX.regs_out0).
Lemma KS_apaHX_ok : BG.kept_ok 80 PapaHX.regs0 PapaHX.regs_out0 KS_apaHX = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaHX_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 17) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u8_at RSEGS M ((V 33%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae0cc M) (st fx' R' 0xae510 M')
        /\ (forall x, In x KS_apaHX -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaHX.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaHX.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaHX.kn0).
  { unfold know_ok, PapaHX.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | byte_tac ltac:(clear) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K52]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaHX.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaHX.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaHX.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaHX.ps0) with 0xae510 in Hms. change (SR.ps_regs PapaHX.ps0) with (map (fun i => (i, nth i PapaHX.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaHX.ps0) with PapaHX.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaHX.regs0 PapaHX.regs_out0 80 KS_apaHX KS_apaHX_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaHX.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaHX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaHX.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaHX.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaH0 := LibSegBa_apaH0_b.
Definition KS_apaH0 : list nat := Eval vm_compute in (BG.kept_list 80 PapaH0.regs0 PapaH0.regs_out0).
Lemma KS_apaH0_ok : BG.kept_ok 80 PapaH0.regs0 PapaH0.regs_out0 KS_apaH0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaH0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 17) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u8_at RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 ->
  (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) -> aligned (V 42%nat) 8 -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 256)) ->
  (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) -> L5.u32_at RSEGS M ((V 42%nat) - 40) (V 40%nat) ->
  L5KA.zeros_at M ((((V 42%nat) - 40) / 8) + 2147450880) 1 -> 0 <= (V 40%nat) <= 0 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae0cc M) (st fx' R' 0xae13c M')
        /\ (forall x, In x KS_apaH0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 42%nat) - 40)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((((V 42%nat) - 40) / 8) + 2147450880)
        /\ getr R' (reg 14) = Z_to_bv 64 713020
        /\ getr R' (reg 15) = Z_to_bv 64 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 pvzI12 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 pvzI13 K44 K45 K46 K47 K48 K49 K50 K51 K52 pvzI14 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K43l; move K43l before pvzI13; pose proof (proj2 pvzI13) as K43r; move K43r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K53l; move K53l before pvzI14; pose proof (proj2 pvzI14) as K53r; move K53r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 40%nat => vz_40 | 42%nat => vz_42 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaH0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaH0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaH0.kn0).
  { unfold know_ok, PapaH0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | byte_tac ltac:(clear) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | clear; lia | exact K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear - HV40l HV40r K53l K53r) | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | exactA K51]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K53l K53r) | exact (conj K53l K53r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K64]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaH0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaH0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaH0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaH0.ps0) with 0xae13c in Hms. change (SR.ps_regs PapaH0.ps0) with (map (fun i => (i, nth i PapaH0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaH0.ps0) with PapaH0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaH0.regs0 PapaH0.regs_out0 80 KS_apaH0 KS_apaH0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaH0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PapaH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PapaH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaH0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PapaH0.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaH1 := LibSegBa_apaH1_b.
Definition KS_apaH1 : list nat := Eval vm_compute in (BG.kept_list 80 PapaH1.regs0 PapaH1.regs_out0).
Lemma KS_apaH1_ok : BG.kept_ok 80 PapaH1.regs0 PapaH1.regs_out0 KS_apaH1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaH1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 17) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u8_at RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 ->
  (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) -> aligned (V 42%nat) 8 -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 256)) ->
  (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) -> L5.u32_at RSEGS M ((V 42%nat) - 40) (V 40%nat) ->
  L5KA.zeros_at M ((((V 42%nat) - 40) / 8) + 2147450880) 1 -> 1 <= (V 40%nat) <= 1 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae0cc M) (st fx' R' 0xae330 M')
        /\ (forall x, In x KS_apaH1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 42%nat) - 40)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((((V 42%nat) - 40) / 8) + 2147450880)
        /\ getr R' (reg 14) = Z_to_bv 64 713520
        /\ getr R' (reg 15) = Z_to_bv 64 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 pvzI12 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 pvzI13 K44 K45 K46 K47 K48 K49 K50 K51 K52 pvzI14 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K43l; move K43l before pvzI13; pose proof (proj2 pvzI13) as K43r; move K43r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K53l; move K53l before pvzI14; pose proof (proj2 pvzI14) as K53r; move K53r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 40%nat => vz_40 | 42%nat => vz_42 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaH1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaH1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaH1.kn0).
  { unfold know_ok, PapaH1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | byte_tac ltac:(clear) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | clear; lia | exact K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear - HV40l HV40r K53l K53r) | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | exactA K51]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K53l K53r) | exact (conj K53l K53r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K64]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaH1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaH1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaH1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaH1.ps0) with 0xae330 in Hms. change (SR.ps_regs PapaH1.ps0) with (map (fun i => (i, nth i PapaH1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaH1.ps0) with PapaH1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaH1.regs0 PapaH1.regs_out0 80 KS_apaH1 KS_apaH1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaH1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PapaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PapaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaH1.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PapaH1.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaH2 := LibSegBa_apaH2_b.
Definition KS_apaH2 : list nat := Eval vm_compute in (BG.kept_list 80 PapaH2.regs0 PapaH2.regs_out0).
Lemma KS_apaH2_ok : BG.kept_ok 80 PapaH2.regs0 PapaH2.regs_out0 KS_apaH2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaH2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 17) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u8_at RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 ->
  (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) -> aligned (V 42%nat) 8 -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 256)) ->
  (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) -> L5.u32_at RSEGS M ((V 42%nat) - 40) (V 40%nat) ->
  L5KA.zeros_at M ((((V 42%nat) - 40) / 8) + 2147450880) 1 -> 2 <= (V 40%nat) <= 2 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae0cc M) (st fx' R' 0xae19c M')
        /\ (forall x, In x KS_apaH2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 42%nat) - 40)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((((V 42%nat) - 40) / 8) + 2147450880)
        /\ getr R' (reg 14) = Z_to_bv 64 713116
        /\ getr R' (reg 15) = Z_to_bv 64 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 pvzI12 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 pvzI13 K44 K45 K46 K47 K48 K49 K50 K51 K52 pvzI14 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K43l; move K43l before pvzI13; pose proof (proj2 pvzI13) as K43r; move K43r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K53l; move K53l before pvzI14; pose proof (proj2 pvzI14) as K53r; move K53r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 40%nat => vz_40 | 42%nat => vz_42 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaH2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaH2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaH2.kn0).
  { unfold know_ok, PapaH2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | byte_tac ltac:(clear) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | clear; lia | exact K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear - HV40l HV40r K53l K53r) | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | exactA K51]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K53l K53r) | exact (conj K53l K53r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K64]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaH2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaH2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaH2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaH2.ps0) with 0xae19c in Hms. change (SR.ps_regs PapaH2.ps0) with (map (fun i => (i, nth i PapaH2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaH2.ps0) with PapaH2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaH2.regs0 PapaH2.regs_out0 80 KS_apaH2 KS_apaH2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaH2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PapaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PapaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaH2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PapaH2.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaH3 := LibSegBa_apaH3_b.
Definition KS_apaH3 : list nat := Eval vm_compute in (BG.kept_list 80 PapaH3.regs0 PapaH3.regs_out0).
Lemma KS_apaH3_ok : BG.kept_ok 80 PapaH3.regs0 PapaH3.regs_out0 KS_apaH3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaH3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 17) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u8_at RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 ->
  (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) -> aligned (V 42%nat) 8 -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 256)) ->
  (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) -> L5.u32_at RSEGS M ((V 42%nat) - 40) (V 40%nat) ->
  L5KA.zeros_at M ((((V 42%nat) - 40) / 8) + 2147450880) 1 -> 3 <= (V 40%nat) <= 3 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae0cc M) (st fx' R' 0xae27c M')
        /\ (forall x, In x KS_apaH3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 42%nat) - 40)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((((V 42%nat) - 40) / 8) + 2147450880)
        /\ getr R' (reg 14) = Z_to_bv 64 713340
        /\ getr R' (reg 15) = Z_to_bv 64 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 pvzI12 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 pvzI13 K44 K45 K46 K47 K48 K49 K50 K51 K52 pvzI14 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K43l; move K43l before pvzI13; pose proof (proj2 pvzI13) as K43r; move K43r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K53l; move K53l before pvzI14; pose proof (proj2 pvzI14) as K53r; move K53r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 40%nat => vz_40 | 42%nat => vz_42 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaH3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaH3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaH3.kn0).
  { unfold know_ok, PapaH3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | byte_tac ltac:(clear) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | clear; lia | exact K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear - HV40l HV40r K53l K53r) | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | exactA K51]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K53l K53r) | exact (conj K53l K53r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K64]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaH3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaH3.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaH3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaH3.ps0) with 0xae27c in Hms. change (SR.ps_regs PapaH3.ps0) with (map (fun i => (i, nth i PapaH3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaH3.ps0) with PapaH3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaH3.regs0 PapaH3.regs_out0 80 KS_apaH3 KS_apaH3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaH3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaH3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaH3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaH3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PapaH3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH3.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PapaH3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaH3.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PapaH3.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaH4 := LibSegBa_apaH4_b.
Definition KS_apaH4 : list nat := Eval vm_compute in (BG.kept_list 80 PapaH4.regs0 PapaH4.regs_out0).
Lemma KS_apaH4_ok : BG.kept_ok 80 PapaH4.regs0 PapaH4.regs_out0 KS_apaH4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaH4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 17) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u8_at RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 ->
  (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) -> aligned (V 42%nat) 8 -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 256)) ->
  (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) -> L5.u32_at RSEGS M ((V 42%nat) - 40) (V 40%nat) ->
  L5KA.zeros_at M ((((V 42%nat) - 40) / 8) + 2147450880) 1 -> 4 <= (V 40%nat) <= 4 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae0cc M) (st fx' R' 0xae160 M')
        /\ (forall x, In x KS_apaH4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 42%nat) - 40)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((((V 42%nat) - 40) / 8) + 2147450880)
        /\ getr R' (reg 14) = Z_to_bv 64 713056
        /\ getr R' (reg 15) = Z_to_bv 64 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 pvzI12 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 pvzI13 K44 K45 K46 K47 K48 K49 K50 K51 K52 pvzI14 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K43l; move K43l before pvzI13; pose proof (proj2 pvzI13) as K43r; move K43r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K53l; move K53l before pvzI14; pose proof (proj2 pvzI14) as K53r; move K53r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 40%nat => vz_40 | 42%nat => vz_42 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaH4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaH4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaH4.kn0).
  { unfold know_ok, PapaH4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | byte_tac ltac:(clear) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | clear; lia | exact K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K50) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear - HV40l HV40r K53l K53r) | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | exactA K51]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | clear - HV42l HV42r K43l K43r K44 K46 K47 K48 K49 K50; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K53l K53r) | exact (conj K53l K53r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K49) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K47) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K47; lia | exactA K64]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaH4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaH4.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaH4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaH4.ps0) with 0xae160 in Hms. change (SR.ps_regs PapaH4.ps0) with (map (fun i => (i, nth i PapaH4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaH4.ps0) with PapaH4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaH4.regs0 PapaH4.regs_out0 80 KS_apaH4 KS_apaH4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaH4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaH4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaH4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaH4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PapaH4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaH4.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PapaH4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaH4.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PapaH4.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaR := LibSegBa_apaR_b.
Definition KS_apaR : list nat := Eval vm_compute in (BG.kept_list 80 PapaR.regs0 PapaR.regs_out0).
Lemma KS_apaR_ok : BG.kept_ok 80 PapaR.regs0 PapaR.regs_out0 KS_apaR = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 ((V 42%nat) - 40) -> getr R (reg 11) = Z_to_bv 64 (V 42%nat) -> getr R (reg 12) = Z_to_bv 64 0 -> getr R (reg 13) = Z_to_bv 64 ((((V 42%nat) - 40) / 8) + 2147450880) -> getr R (reg 14) = Z_to_bv 64 713020 -> getr R (reg 15) = Z_to_bv 64 4 -> getr R (reg 17) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 -> (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) ->
  aligned (V 42%nat) 8 -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 256)) -> (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) ->
  (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) -> L5.u32_at RSEGS M ((V 42%nat) - 40) (V 40%nat) -> L5KA.zeros_at M ((((V 42%nat) - 40) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M ((V 42%nat) - 40) 4 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 42%nat) - 40) <= bv_unsigned a < ((V 42%nat) - 40) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 42%nat) - 40) <= i < ((V 42%nat) - 40) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae13c M) (st fx' R' 0xae924 M')
        /\ (forall x, In x KS_apaR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 713052
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 42%nat) - 40) 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G12 G13 G14 G15 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 pvzI12 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI13 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K42l; move K42l before pvzI13; pose proof (proj2 pvzI13) as K42r; move K42r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 40%nat => vz_40 | 42%nat => vz_42 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaR.kn0).
  { unfold know_ok, PapaR.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | clear; lia | exact K44]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K50]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K63]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaR.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_42 - 40) <= bv_unsigned a < (vz_42 - 40) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapaR.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaR.ps0) with 0xae924 in Hms. change (SR.ps_regs PapaR.ps0) with (map (fun i => (i, nth i PapaR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaR.ps0) with PapaR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaR.regs0 PapaR.regs_out0 80 KS_apaR KS_apaR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapaR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaR.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaR.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaV := LibSegBa_apaV_b.
Definition KS_apaV : list nat := Eval vm_compute in (BG.kept_list 80 PapaV.regs0 PapaV.regs_out0).
Lemma KS_apaV_ok : BG.kept_ok 80 PapaV.regs0 PapaV.regs_out0 KS_apaV = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaV_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 ((V 42%nat) - 40) -> getr R (reg 11) = Z_to_bv 64 (V 42%nat) -> getr R (reg 12) = Z_to_bv 64 0 -> getr R (reg 13) = Z_to_bv 64 ((((V 42%nat) - 40) / 8) + 2147450880) -> getr R (reg 14) = Z_to_bv 64 713056 -> getr R (reg 15) = Z_to_bv 64 4 -> getr R (reg 17) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 -> (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) ->
  aligned (V 42%nat) 8 -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 256)) -> (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) ->
  (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) -> L5.u32_at RSEGS M ((V 42%nat) - 40) (V 40%nat) -> L5KA.zeros_at M ((((V 42%nat) - 40) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M ((V 42%nat) - 16) (V 44%nat) -> 0 <= (V 44%nat) <= 255 -> L5KA.zeros_at M ((((V 42%nat) - 16) / 8) + 2147450880) 1 -> L5.writable RSEGS M ((V 42%nat) - 40) 4 ->
  L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 42%nat) - 40) <= bv_unsigned a < ((V 42%nat) - 40) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 42%nat) - 40) <= i < ((V 42%nat) - 40) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae160 M) (st fx' R' 0xaff88 M')
        /\ (forall x, In x KS_apaV -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 713112
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 42%nat) - 40) 2).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G11 G12 G13 G14 G15 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 K13 pvzI12 K15 K16 K17 K18 K19 K20 pvzI13 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI14 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 pvzI15 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV51l; move HV51l before pvzI9; pose proof (proj2 pvzI9) as HV51r; move HV51r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K21l; move K21l before pvzI13; pose proof (proj2 pvzI13) as K21r; move K21r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K42l; move K42l before pvzI14; pose proof (proj2 pvzI14) as K42r; move K42r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K53l; move K53l before pvzI15; pose proof (proj2 pvzI15) as K53r; move K53r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 44%nat => Z_to_bv 64 vz_44 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 40%nat => vz_40 | 42%nat => vz_42 | 44%nat => vz_44 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaV.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaV.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaV.kn0).
  { unfold know_ok, PapaV.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | clear; lia | exact K44]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K50]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear - HV44l HV44r K53l K53r) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | byte_tac ltac:(clear - HV44l HV44r K53l K53r) | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K53l K53r) | exact (conj K53l K53r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K66]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaV.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaV.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_42 - 40) <= bv_unsigned a < (vz_42 - 40) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapaV.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaV.ps0) with 0xaff88 in Hms. change (SR.ps_regs PapaV.ps0) with (map (fun i => (i, nth i PapaV.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaV.ps0) with PapaV.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaV.regs0 PapaV.regs_out0 80 KS_apaV KS_apaV_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaV.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapaV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaV.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaV.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaV.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaV.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PapaV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaD1 := LibSegBa_apaD1_b.
Definition KS_apaD1 : list nat := Eval vm_compute in (BG.kept_list 80 PapaD1.regs0 PapaD1.regs_out0).
Lemma KS_apaD1_ok : BG.kept_ok 80 PapaD1.regs0 PapaD1.regs_out0 KS_apaD1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaD1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 12) = Z_to_bv 64 0 -> getr R (reg 14) = Z_to_bv 64 713116 -> getr R (reg 15) = Z_to_bv 64 4 -> getr R (reg 17) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= i < ((((V 50%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae19c M) (st fx' R' 0xaed4c M')
        /\ (forall x, In x KS_apaD1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 713140
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G14 G15 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaD1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaD1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaD1.kn0).
  { unfold know_ok, PapaD1.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K51]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaD1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaD1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_50 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapaD1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaD1.ps0) with 0xaed4c in Hms. change (SR.ps_regs PapaD1.ps0) with (map (fun i => (i, nth i PapaD1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaD1.ps0) with PapaD1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaD1.regs0 PapaD1.regs_out0 80 KS_apaD1 KS_apaD1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaD1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapaD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaD1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaD2 := LibSegBa_apaD2_b.
Definition KS_apaD2 : list nat := Eval vm_compute in (BG.kept_list 80 PapaD2.regs0 PapaD2.regs_out0).
Lemma KS_apaD2_ok : BG.kept_ok 80 PapaD2.regs0 PapaD2.regs_out0 KS_apaD2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaD2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 46%nat) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 -> (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) ->
  aligned (V 42%nat) 8 -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 256)) -> (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) ->
  (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) -> L5.u32_at RSEGS M ((V 42%nat) - 40) (V 40%nat) -> L5KA.zeros_at M ((((V 42%nat) - 40) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 42%nat) - 24) (V 43%nat) -> L5KA.zeros_at M ((((V 42%nat) - 24) / 8) + 2147450880) 1 -> 0 <= (V 46%nat) <= 1 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae1b4 M) (st fx' R' 0xae1f0 M')
        /\ (forall x, In x KS_apaD2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) - 24)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 43%nat) + (V 46%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI11 K4 K5 pvzI12 K7 K8 K9 K10 K11 K12 K13 pvzI13 K15 K16 K17 K18 K19 K20 pvzI14 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI15 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 pvzI16 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K6l; move K6l before pvzI12; pose proof (proj2 pvzI12) as K6r; move K6r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K14l; move K14l before pvzI13; pose proof (proj2 pvzI13) as K14r; move K14r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K21l; move K21l before pvzI14; pose proof (proj2 pvzI14) as K21r; move K21r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K42l; move K42l before pvzI15; pose proof (proj2 pvzI15) as K42r; move K42r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K54l; move K54l before pvzI16; pose proof (proj2 pvzI16) as K54r; move K54r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 40%nat => vz_40 | 42%nat => vz_42 | 43%nat => vz_43 | 46%nat => vz_46 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaD2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaD2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaD2.kn0).
  { unfold know_ok, PapaD2.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | clear; lia | exact K44]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K50]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K52]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K54l K54r) | exact (conj K54l K54r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K65]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaD2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaD2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaD2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaD2.ps0) with 0xae1f0 in Hms. change (SR.ps_regs PapaD2.ps0) with (map (fun i => (i, nth i PapaD2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaD2.ps0) with PapaD2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaD2.regs0 PapaD2.regs_out0 80 KS_apaD2 KS_apaD2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaD2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaD2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaD2.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaD3 := LibSegBa_apaD3_b.
Definition KS_apaD3 : list nat := Eval vm_compute in (BG.kept_list 80 PapaD3.regs0 PapaD3.regs_out0).
Lemma KS_apaD3_ok : BG.kept_ok 80 PapaD3.regs0 PapaD3.regs_out0 KS_apaD3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaD3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 46%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 42%nat) - 24) -> getr R (reg 12) = Z_to_bv 64 (V 49%nat) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 ->
  (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) -> aligned (V 42%nat) 8 -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 256)) ->
  (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) -> L5.u32_at RSEGS M ((V 42%nat) - 40) (V 40%nat) ->
  L5KA.zeros_at M ((((V 42%nat) - 40) / 8) + 2147450880) 1 -> L5.writable RSEGS M ((V 42%nat) - 24) 8 -> 0 <= (V 49%nat) <= 18446744073709551615 -> 0 <= (V 46%nat) <= 1 ->
  L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 42%nat) - 24) <= bv_unsigned a < ((V 42%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 42%nat) - 24) <= i < ((V 42%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae1f0 M) (st fx' R' 0xae1f4 M')
        /\ (forall x, In x KS_apaD3 -> getr R' (reg x) = getr R (reg x))
        /\ L5.u64_at RSEGS M' ((V 42%nat) - 24) (V 49%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI11 K4 K5 pvzI12 K7 K8 K9 K10 K11 K12 K13 pvzI13 K15 K16 K17 K18 K19 K20 pvzI14 K22 K23 K24 K25 K26 K27 K28 K29 K30 pvzI15 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI16 pvzI17 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV49l; move HV49l before pvzI8; pose proof (proj2 pvzI8) as HV49r; move HV49r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K6l; move K6l before pvzI12; pose proof (proj2 pvzI12) as K6r; move K6r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K14l; move K14l before pvzI13; pose proof (proj2 pvzI13) as K14r; move K14r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K21l; move K21l before pvzI14; pose proof (proj2 pvzI14) as K21r; move K21r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K31l; move K31l before pvzI15; pose proof (proj2 pvzI15) as K31r; move K31r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K42l; move K42l before pvzI16; pose proof (proj2 pvzI16) as K42r; move K42r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K43l; move K43l before pvzI17; pose proof (proj2 pvzI17) as K43r; move K43r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 46%nat => Z_to_bv 64 vz_46 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 40%nat => vz_40 | 42%nat => vz_42 | 46%nat => vz_46 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaD3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaD3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaD3.kn0).
  { unfold know_ok, PapaD3.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K38) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | exactA K39]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K43l K43r) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K56]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaD3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaD3.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_42 - 24) <= bv_unsigned a < (vz_42 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapaD3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk' ZA Hag ltac:(clear) | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaD3.ps0) with 0xae1f4 in Hms. change (SR.ps_regs PapaD3.ps0) with (map (fun i => (i, nth i PapaD3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaD3.ps0) with PapaD3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaD3.regs0 PapaD3.regs_out0 80 KS_apaD3 KS_apaD3_ok HR Hag Hregs j Hj). }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk' ZA Hag ltac:(clear - HV49l HV49r K42l K42r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaD4e := LibSegBa_apaD4e_b.
Definition KS_apaD4e : list nat := Eval vm_compute in (BG.kept_list 80 PapaD4e.regs0 PapaD4e.regs_out0).
Lemma KS_apaD4e_ok : BG.kept_ok 80 PapaD4e.regs0 PapaD4e.regs_out0 KS_apaD4e = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaD4e_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae1f4 M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_apaD4e -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 713884
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaD4e.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaD4e.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaD4e.kn0).
  { unfold know_ok, PapaD4e.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K51]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaD4e.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaD4e.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaD4e.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaD4e.ps0) with 0xae848 in Hms. change (SR.ps_regs PapaD4e.ps0) with (map (fun i => (i, nth i PapaD4e.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaD4e.ps0) with PapaD4e.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaD4e.regs0 PapaD4e.regs_out0 80 KS_apaD4e KS_apaD4e_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaD4e.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapaD4e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD4e.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaD4e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaD4e.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaD4e.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaD4z := LibSegBa_apaD4z_b.
Definition KS_apaD4z : list nat := Eval vm_compute in (BG.kept_list 80 PapaD4z.regs0 PapaD4z.regs_out0).
Lemma KS_apaD4z_ok : BG.kept_ok 80 PapaD4z.regs0 PapaD4z.regs_out0 KS_apaD4z = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaD4z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u8_at RSEGS M ((V 50%nat) + 32) (V 45%nat) -> 0 <= (V 45%nat) <= 0 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae1f4 M) (st fx' R' 0xaf9e0 M')
        /\ (forall x, In x KS_apaD4z -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 713664
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 K20 pvzI11 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI12 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K21l; move K21l before pvzI11; pose proof (proj2 pvzI11) as K21r; move K21r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K42l; move K42l before pvzI12; pose proof (proj2 pvzI12) as K42r; move K42r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 45%nat => Z_to_bv 64 vz_45 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 45%nat => vz_45 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaD4z.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaD4z.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaD4z.kn0).
  { unfold know_ok, PapaD4z.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV45l HV45r K42l K42r) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | byte_tac ltac:(clear - HV45l HV45r K42l K42r) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K53]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaD4z.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaD4z.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaD4z.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaD4z.ps0) with 0xaf9e0 in Hms. change (SR.ps_regs PapaD4z.ps0) with (map (fun i => (i, nth i PapaD4z.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaD4z.ps0) with PapaD4z.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaD4z.regs0 PapaD4z.regs_out0 80 KS_apaD4z KS_apaD4z_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaD4z.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapaD4z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD4z.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaD4z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD4z.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaD4z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaD4z.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaD4z.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaD4n := LibSegBa_apaD4n_b.
Definition KS_apaD4n : list nat := Eval vm_compute in (BG.kept_list 80 PapaD4n.regs0 PapaD4n.regs_out0).
Lemma KS_apaD4n_ok : BG.kept_ok 80 PapaD4n.regs0 PapaD4n.regs_out0 KS_apaD4n = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaD4n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u8_at RSEGS M ((V 50%nat) + 32) (V 45%nat) -> 1 <= (V 45%nat) <= 255 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae1f4 M) (st fx' R' 0xaf548 M')
        /\ (forall x, In x KS_apaD4n -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 713244
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 K20 pvzI11 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI12 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K21l; move K21l before pvzI11; pose proof (proj2 pvzI11) as K21r; move K21r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K42l; move K42l before pvzI12; pose proof (proj2 pvzI12) as K42r; move K42r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 45%nat => Z_to_bv 64 vz_45 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 45%nat => vz_45 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaD4n.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaD4n.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaD4n.kn0).
  { unfold know_ok, PapaD4n.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV45l HV45r K42l K42r) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | byte_tac ltac:(clear - HV45l HV45r K42l K42r) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K53]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaD4n.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaD4n.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaD4n.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaD4n.ps0) with 0xaf548 in Hms. change (SR.ps_regs PapaD4n.ps0) with (map (fun i => (i, nth i PapaD4n.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaD4n.ps0) with PapaD4n.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaD4n.regs0 PapaD4n.regs_out0 80 KS_apaD4n KS_apaD4n_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaD4n.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapaD4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD4n.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaD4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD4n.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaD4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD4n.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaD4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaD4n.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PapaD4n.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaDE := LibSegBa_apaDE_b.
Definition KS_apaDE : list nat := Eval vm_compute in (BG.kept_list 80 PapaDE.regs0 PapaDE.regs_out0).
Lemma KS_apaDE_ok : BG.kept_ok 80 PapaDE.regs0 PapaDE.regs_out0 KS_apaDE = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaDE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= i < ((((V 50%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae49c M) (st fx' R' 0xae510 M')
        /\ (forall x, In x KS_apaDE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551608
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaDE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaDE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaDE.kn0).
  { unfold know_ok, PapaDE.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K52]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaDE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaDE.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> ~ ((((vz_50 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PapaDE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaDE.ps0) with 0xae510 in Hms. change (SR.ps_regs PapaDE.ps0) with (map (fun i => (i, nth i PapaDE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaDE.ps0) with PapaDE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaDE.regs0 PapaDE.regs_out0 80 KS_apaDE KS_apaDE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaDE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaDE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaDZ := LibSegBa_apaDZ_b.
Definition KS_apaDZ : list nat := Eval vm_compute in (BG.kept_list 80 PapaDZ.regs0 PapaDZ.regs_out0).
Lemma KS_apaDZ_ok : BG.kept_ok 80 PapaDZ.regs0 PapaDZ.regs_out0 KS_apaDZ = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaDZ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= i < ((((V 50%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae3c0 M) (st fx' R' 0xae3fc M')
        /\ (forall x, In x KS_apaDZ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaDZ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaDZ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaDZ.kn0).
  { unfold know_ok, PapaDZ.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaDZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaDZ.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_50 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapaDZ.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaDZ.ps0) with 0xae3fc in Hms. change (SR.ps_regs PapaDZ.ps0) with (map (fun i => (i, nth i PapaDZ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaDZ.ps0) with PapaDZ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaDZ.regs0 PapaDZ.regs_out0 80 KS_apaDZ KS_apaDZ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaDZ.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaDZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaDZ.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PapaDZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaY1 := LibSegBa_apaY1_b.
Definition KS_apaY1 : list nat := Eval vm_compute in (BG.kept_list 80 PapaY1.regs0 PapaY1.regs_out0).
Lemma KS_apaY1_ok : BG.kept_ok 80 PapaY1.regs0 PapaY1.regs_out0 KS_apaY1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaY1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 12) = Z_to_bv 64 0 -> getr R (reg 14) = Z_to_bv 64 713340 -> getr R (reg 15) = Z_to_bv 64 4 -> getr R (reg 17) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 6) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 6) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 6) <= i < ((((V 50%nat) / 8) + 2147450880) + 6) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae27c M) (st fx' R' 0xaed4c M')
        /\ (forall x, In x KS_apaY1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 713364
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 48)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G12 G14 G15 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaY1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaY1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaY1.kn0).
  { unfold know_ok, PapaY1.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K51]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaY1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaY1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_50 / 8) + 2147450880) + 6) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 6) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapaY1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaY1.ps0) with 0xaed4c in Hms. change (SR.ps_regs PapaY1.ps0) with (map (fun i => (i, nth i PapaY1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaY1.ps0) with PapaY1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaY1.regs0 PapaY1.regs_out0 80 KS_apaY1 KS_apaY1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaY1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapaY1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaY1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaY1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaY1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaY2 := LibSegBa_apaY2_b.
Definition KS_apaY2 : list nat := Eval vm_compute in (BG.kept_list 80 PapaY2.regs0 PapaY2.regs_out0).
Lemma KS_apaY2_ok : BG.kept_ok 80 PapaY2.regs0 PapaY2.regs_out0 KS_apaY2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaY2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 46%nat) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 -> (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) ->
  aligned (V 42%nat) 8 -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 256)) -> (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) ->
  (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) -> L5.u32_at RSEGS M ((V 42%nat) - 40) (V 40%nat) -> L5KA.zeros_at M ((((V 42%nat) - 40) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 42%nat) - 24) (V 43%nat) -> L5KA.zeros_at M ((((V 42%nat) - 24) / 8) + 2147450880) 1 -> 0 <= (V 46%nat) <= 1 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae294 M) (st fx' R' 0xae2d4 M')
        /\ (forall x, In x KS_apaY2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) - 24)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 43%nat) + (V 46%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 50%nat) + 48)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI11 K4 K5 pvzI12 K7 K8 K9 K10 K11 K12 K13 pvzI13 K15 K16 K17 K18 K19 K20 pvzI14 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI15 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 pvzI16 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K6l; move K6l before pvzI12; pose proof (proj2 pvzI12) as K6r; move K6r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K14l; move K14l before pvzI13; pose proof (proj2 pvzI13) as K14r; move K14r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K21l; move K21l before pvzI14; pose proof (proj2 pvzI14) as K21r; move K21r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K42l; move K42l before pvzI15; pose proof (proj2 pvzI15) as K42r; move K42r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K54l; move K54l before pvzI16; pose proof (proj2 pvzI16) as K54r; move K54r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 40%nat => vz_40 | 42%nat => vz_42 | 43%nat => vz_43 | 46%nat => vz_46 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaY2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaY2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaY2.kn0).
  { unfold know_ok, PapaY2.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | clear; lia | exact K44]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K50]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K52]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K54l K54r) | exact (conj K54l K54r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K65]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaY2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaY2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaY2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaY2.ps0) with 0xae2d4 in Hms. change (SR.ps_regs PapaY2.ps0) with (map (fun i => (i, nth i PapaY2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaY2.ps0) with PapaY2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaY2.regs0 PapaY2.regs_out0 80 KS_apaY2 KS_apaY2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaY2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaY2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaY2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaY2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PapaY2.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaY3 := LibSegBa_apaY3_b.
Definition KS_apaY3 : list nat := Eval vm_compute in (BG.kept_list 80 PapaY3.regs0 PapaY3.regs_out0).
Lemma KS_apaY3_ok : BG.kept_ok 80 PapaY3.regs0 PapaY3.regs_out0 KS_apaY3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaY3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 46%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 42%nat) - 24) -> getr R (reg 12) = Z_to_bv 64 (V 49%nat) -> getr R (reg 13) = Z_to_bv 64 ((V 50%nat) + 48) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 ->
  (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) -> aligned (V 42%nat) 8 -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 256)) ->
  (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) -> L5.u32_at RSEGS M ((V 42%nat) - 40) (V 40%nat) ->
  L5KA.zeros_at M ((((V 42%nat) - 40) / 8) + 2147450880) 1 -> L5.writable RSEGS M ((V 42%nat) - 24) 8 -> 0 <= (V 49%nat) <= 18446744073709551615 -> 0 <= (V 46%nat) <= 1 ->
  L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 42%nat) - 24) <= bv_unsigned a < ((V 42%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 42%nat) - 24) <= i < ((V 42%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae2d4 M) (st fx' R' 0xae2d8 M')
        /\ (forall x, In x KS_apaY3 -> getr R' (reg x) = getr R (reg x))
        /\ L5.u64_at RSEGS M' ((V 42%nat) - 24) (V 49%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G11 G12 G13 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI11 K4 K5 pvzI12 K7 K8 K9 K10 K11 K12 K13 pvzI13 K15 K16 K17 K18 K19 K20 pvzI14 K22 K23 K24 K25 K26 K27 K28 K29 K30 pvzI15 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI16 pvzI17 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV49l; move HV49l before pvzI8; pose proof (proj2 pvzI8) as HV49r; move HV49r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K6l; move K6l before pvzI12; pose proof (proj2 pvzI12) as K6r; move K6r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K14l; move K14l before pvzI13; pose proof (proj2 pvzI13) as K14r; move K14r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K21l; move K21l before pvzI14; pose proof (proj2 pvzI14) as K21r; move K21r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K31l; move K31l before pvzI15; pose proof (proj2 pvzI15) as K31r; move K31r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K42l; move K42l before pvzI16; pose proof (proj2 pvzI16) as K42r; move K42r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K43l; move K43l before pvzI17; pose proof (proj2 pvzI17) as K43r; move K43r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 46%nat => Z_to_bv 64 vz_46 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 40%nat => vz_40 | 42%nat => vz_42 | 46%nat => vz_46 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaY3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaY3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaY3.kn0).
  { unfold know_ok, PapaY3.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K38) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | exactA K39]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K43l K43r) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K37) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K35) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K36) | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K35; lia | exactA K56]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaY3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaY3.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_42 - 24) <= bv_unsigned a < (vz_42 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapaY3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk' ZA Hag ltac:(clear) | clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaY3.ps0) with 0xae2d8 in Hms. change (SR.ps_regs PapaY3.ps0) with (map (fun i => (i, nth i PapaY3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaY3.ps0) with PapaY3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaY3.regs0 PapaY3.regs_out0 80 KS_apaY3 KS_apaY3_ok HR Hag Hregs j Hj). }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV42l HV42r K31l K31r K32 K34 K35 K36 K37 K38) | evalEk' ZA Hag ltac:(clear - HV49l HV49r K42l K42r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaY4e := LibSegBa_apaY4e_b.
Definition KS_apaY4e : list nat := Eval vm_compute in (BG.kept_list 80 PapaY4e.regs0 PapaY4e.regs_out0).
Lemma KS_apaY4e_ok : BG.kept_ok 80 PapaY4e.regs0 PapaY4e.regs_out0 KS_apaY4e = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaY4e_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 13) = Z_to_bv 64 ((V 50%nat) + 48) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae2d8 M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_apaY4e -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 713928
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaY4e.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaY4e.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaY4e.kn0).
  { unfold know_ok, PapaY4e.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K51]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaY4e.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaY4e.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaY4e.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaY4e.ps0) with 0xae848 in Hms. change (SR.ps_regs PapaY4e.ps0) with (map (fun i => (i, nth i PapaY4e.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaY4e.ps0) with PapaY4e.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaY4e.regs0 PapaY4e.regs_out0 80 KS_apaY4e KS_apaY4e_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaY4e.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapaY4e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4e.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaY4e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaY4e.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaY4e.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaY4z := LibSegBa_apaY4z_b.
Definition KS_apaY4z : list nat := Eval vm_compute in (BG.kept_list 80 PapaY4z.regs0 PapaY4z.regs_out0).
Lemma KS_apaY4z_ok : BG.kept_ok 80 PapaY4z.regs0 PapaY4z.regs_out0 KS_apaY4z = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaY4z_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 13) = Z_to_bv 64 ((V 50%nat) + 48) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u8_at RSEGS M ((V 50%nat) + 48) (V 45%nat) -> 0 <= (V 45%nat) <= 0 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae2d8 M) (st fx' R' 0xb1c9c M')
        /\ (forall x, In x KS_apaY4z -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 713696
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 9)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 33%nat) + 392)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 K20 pvzI11 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI12 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K21l; move K21l before pvzI11; pose proof (proj2 pvzI11) as K21r; move K21r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K42l; move K42l before pvzI12; pose proof (proj2 pvzI12) as K42r; move K42r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 45%nat => Z_to_bv 64 vz_45 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 45%nat => vz_45 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaY4z.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaY4z.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaY4z.kn0).
  { unfold know_ok, PapaY4z.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV45l HV45r K42l K42r) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | byte_tac ltac:(clear - HV45l HV45r K42l K42r) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K53]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaY4z.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaY4z.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaY4z.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaY4z.ps0) with 0xb1c9c in Hms. change (SR.ps_regs PapaY4z.ps0) with (map (fun i => (i, nth i PapaY4z.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaY4z.ps0) with PapaY4z.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaY4z.regs0 PapaY4z.regs_out0 80 KS_apaY4z KS_apaY4z_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaY4z.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapaY4z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4z.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaY4z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4z.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaY4z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4z.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaY4z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4z.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PapaY4z.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaY4z.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PapaY4z.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaY4n := LibSegBa_apaY4n_b.
Definition KS_apaY4n : list nat := Eval vm_compute in (BG.kept_list 80 PapaY4n.regs0 PapaY4n.regs_out0).
Lemma KS_apaY4n_ok : BG.kept_ok 80 PapaY4n.regs0 PapaY4n.regs_out0 KS_apaY4n = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaY4n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 13) = Z_to_bv 64 ((V 50%nat) + 48) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u8_at RSEGS M ((V 50%nat) + 48) (V 45%nat) -> 1 <= (V 45%nat) <= 255 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae2d8 M) (st fx' R' 0xaf548 M')
        /\ (forall x, In x KS_apaY4n -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 713488
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 50%nat) + 48)
        /\ getr R' (reg 20) = Z_to_bv 64 40
        /\ getr R' (reg 21) = Z_to_bv 64 143316
        /\ getr R' (reg 22) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 9)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 33%nat) + 400)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G13 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 K20 pvzI11 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI12 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K21l; move K21l before pvzI11; pose proof (proj2 pvzI11) as K21r; move K21r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K42l; move K42l before pvzI12; pose proof (proj2 pvzI12) as K42r; move K42r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 45%nat => Z_to_bv 64 vz_45 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 45%nat => vz_45 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaY4n.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaY4n.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaY4n.kn0).
  { unfold know_ok, PapaY4n.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV45l HV45r K42l K42r) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | byte_tac ltac:(clear - HV45l HV45r K42l K42r) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K53]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaY4n.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaY4n.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaY4n.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaY4n.ps0) with 0xaf548 in Hms. change (SR.ps_regs PapaY4n.ps0) with (map (fun i => (i, nth i PapaY4n.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaY4n.ps0) with PapaY4n.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaY4n.regs0 PapaY4n.regs_out0 80 KS_apaY4n KS_apaY4n_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaY4n.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapaY4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4n.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaY4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4n.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaY4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4n.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaY4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4n.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PapaY4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4n.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PapaY4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4n.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PapaY4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4n.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PapaY4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4n.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PapaY4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4n.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PapaY4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4n.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PapaY4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4n.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PapaY4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY4n.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PapaY4n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaY4n.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PapaY4n.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaYE := LibSegBa_apaYE_b.
Definition KS_apaYE : list nat := Eval vm_compute in (BG.kept_list 80 PapaYE.regs0 PapaYE.regs_out0).
Lemma KS_apaYE_ok : BG.kept_ok 80 PapaYE.regs0 PapaYE.regs_out0 KS_apaYE = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaYE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> ~ (((((V 50%nat) / 8) + 2147450880) + 6) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 6) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> ~ (((((V 50%nat) / 8) + 2147450880) + 6) <= i < ((((V 50%nat) / 8) + 2147450880) + 6) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae4c8 M) (st fx' R' 0xae510 M')
        /\ (forall x, In x KS_apaYE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551608
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaYE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaYE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaYE.kn0).
  { unfold know_ok, PapaYE.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K52]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaYE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaYE.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> ~ ((((vz_50 / 8) + 2147450880) + 6) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 6) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PapaYE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaYE.ps0) with 0xae510 in Hms. change (SR.ps_regs PapaYE.ps0) with (map (fun i => (i, nth i PapaYE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaYE.ps0) with PapaYE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaYE.regs0 PapaYE.regs_out0 80 KS_apaYE KS_apaYE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaYE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaYE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaYZ := LibSegBa_apaYZ_b.
Definition KS_apaYZ : list nat := Eval vm_compute in (BG.kept_list 80 PapaYZ.regs0 PapaYZ.regs_out0).
Lemma KS_apaYZ_ok : BG.kept_ok 80 PapaYZ.regs0 PapaYZ.regs_out0 KS_apaYZ = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaYZ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 6) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 6) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 6) <= i < ((((V 50%nat) / 8) + 2147450880) + 6) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae3e0 M) (st fx' R' 0xae3fc M')
        /\ (forall x, In x KS_apaYZ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 33%nat) + 9)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaYZ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaYZ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaYZ.kn0).
  { unfold know_ok, PapaYZ.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaYZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaYZ.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_50 / 8) + 2147450880) + 6) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 6) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapaYZ.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaYZ.ps0) with 0xae3fc in Hms. change (SR.ps_regs PapaYZ.ps0) with (map (fun i => (i, nth i PapaYZ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaYZ.ps0) with PapaYZ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaYZ.regs0 PapaYZ.regs_out0 80 KS_apaYZ KS_apaYZ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaYZ.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaYZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaYZ.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaYZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaYZ.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PapaYZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaYZ.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PapaYZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaYZ.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PapaYZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaD5 := LibSegBa_apaD5_b.
Definition KS_apaD5 : list nat := Eval vm_compute in (BG.kept_list 80 PapaD5.regs0 PapaD5.regs_out0).
Lemma KS_apaD5_ok : BG.kept_ok 80 PapaD5.regs0 PapaD5.regs_out0 KS_apaD5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaD5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 -> (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) ->
  aligned (V 42%nat) 8 -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 256)) -> (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) ->
  (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) -> L5.u32_at RSEGS M ((V 42%nat) - 40) (V 40%nat) -> L5KA.zeros_at M ((((V 42%nat) - 40) / 8) + 2147450880) 1 ->
  L5.u8_at RSEGS M ((V 42%nat) - 16) (V 44%nat) -> 0 <= (V 44%nat) <= 255 -> L5KA.zeros_at M ((((V 42%nat) - 16) / 8) + 2147450880) 1 -> L5.writable RSEGS M ((V 42%nat) - 40) 4 ->
  L5.writable RSEGS M ((V 42%nat) - 16) 1 -> L5.u8_at RSEGS M ((V 50%nat) + 32) (V 45%nat) -> 0 <= (V 45%nat) <= 255 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 42%nat) - 40) <= bv_unsigned a < ((V 42%nat) - 40) + 4) -> ~ (((V 42%nat) - 16) <= bv_unsigned a < ((V 42%nat) - 16) + 1) -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 4) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 42%nat) - 40) <= i < ((V 42%nat) - 40) + 4) -> ~ (((V 42%nat) - 16) <= i < ((V 42%nat) - 16) + 1) -> ~ (((((V 50%nat) / 8) + 2147450880) + 4) <= i < ((((V 50%nat) / 8) + 2147450880) + 4) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae21c M) (st fx' R' 0xae3fc M')
        /\ (forall x, In x KS_apaD5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 11) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' ((V 42%nat) - 16) (V 45%nat)
        /\ L5.u32_at RSEGS M' ((V 42%nat) - 40) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI11 K4 K5 pvzI12 K7 K8 K9 K10 K11 K12 K13 pvzI13 K15 K16 K17 K18 K19 K20 pvzI14 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI15 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 pvzI16 K54 K55 K56 K57 pvzI17 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K6l; move K6l before pvzI12; pose proof (proj2 pvzI12) as K6r; move K6r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K14l; move K14l before pvzI13; pose proof (proj2 pvzI13) as K14r; move K14r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K21l; move K21l before pvzI14; pose proof (proj2 pvzI14) as K21r; move K21r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K42l; move K42l before pvzI15; pose proof (proj2 pvzI15) as K42r; move K42r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K53l; move K53l before pvzI16; pose proof (proj2 pvzI16) as K53r; move K53r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K58l; move K58l before pvzI17; pose proof (proj2 pvzI17) as K58r; move K58r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 40%nat => vz_40 | 42%nat => vz_42 | 44%nat => vz_44 | 45%nat => vz_45 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaD5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaD5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaD5.kn0).
  { unfold know_ok, PapaD5.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | clear; lia | exact K44]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K49) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K50]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear - HV44l HV44r K53l K53r) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | byte_tac ltac:(clear - HV44l HV44r K53l K53r) | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K53l K53r) | exact (conj K53l K53r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk ZA ltac:(clear - HV45l HV45r K58l K58r) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48; lia | byte_tac ltac:(clear - HV45l HV45r K58l K58r) | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K58l K58r) | exact (conj K58l K58r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K46) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K47) | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K46; lia | exactA K69]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaD5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaD5.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_42 - 40) <= bv_unsigned a < (vz_42 - 40) + 4) -> ~ ((vz_42 - 16) <= bv_unsigned a < (vz_42 - 16) + 1) -> ~ ((((vz_50 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PapaD5.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaD5.ps0) with 0xae3fc in Hms. change (SR.ps_regs PapaD5.ps0) with (map (fun i => (i, nth i PapaD5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaD5.ps0) with PapaD5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaD5.regs0 PapaD5.regs_out0 80 KS_apaD5 KS_apaD5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaD5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaD5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaD5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaD5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD5.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PapaD5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD5.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PapaD5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk' ZA Hag ltac:(clear - HV45l HV45r K58l K58r) | byte_tac ltac:(clear - HV45l HV45r K58l K58r) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaY5 := LibSegBa_apaY5_b.
Definition KS_apaY5 : list nat := Eval vm_compute in (BG.kept_list 80 PapaY5.regs0 PapaY5.regs_out0).
Lemma KS_apaY5_ok : BG.kept_ok 80 PapaY5.regs0 PapaY5.regs_out0 KS_apaY5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaY5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 50%nat) + 48) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 34%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u8_at RSEGS M ((V 50%nat) + 48) (V 45%nat) -> 0 <= (V 45%nat) <= 255 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae310 M) (st fx' R' 0xaff88 M')
        /\ (forall x, In x KS_apaY5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 713516
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 50%nat) + 48)
        /\ getr R' (reg 20) = Z_to_bv 64 40
        /\ getr R' (reg 21) = Z_to_bv 64 143316
        /\ getr R' (reg 22) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 9)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 33%nat) + 400)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 K20 pvzI11 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI12 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K21l; move K21l before pvzI11; pose proof (proj2 pvzI11) as K21r; move K21r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K42l; move K42l before pvzI12; pose proof (proj2 pvzI12) as K42r; move K42r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 45%nat => Z_to_bv 64 vz_45 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 45%nat => vz_45 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaY5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaY5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaY5.kn0).
  { unfold know_ok, PapaY5.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV45l HV45r K42l K42r) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | byte_tac ltac:(clear - HV45l HV45r K42l K42r) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K53]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaY5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaY5.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaY5.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaY5.ps0) with 0xaff88 in Hms. change (SR.ps_regs PapaY5.ps0) with (map (fun i => (i, nth i PapaY5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaY5.ps0) with PapaY5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaY5.regs0 PapaY5.regs_out0 80 KS_apaY5 KS_apaY5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaY5.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapaY5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaY5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaY5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaY5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY5.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PapaY5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY5.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PapaY5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY5.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PapaY5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY5.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PapaY5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY5.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PapaY5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY5.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PapaY5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY5.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PapaY5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY5.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PapaY5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY5.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PapaY5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaY5.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PapaY5.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaY6 := LibSegBa_apaY6_b.
Definition KS_apaY6 : list nat := Eval vm_compute in (BG.kept_list 80 PapaY6.regs0 PapaY6.regs_out0).
Lemma KS_apaY6_ok : BG.kept_ok 80 PapaY6.regs0 PapaY6.regs_out0 KS_apaY6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaY6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 50%nat) + 48) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 6) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 6) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 6) <= i < ((((V 50%nat) / 8) + 2147450880) + 6) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae32c M) (st fx' R' 0xae3fc M')
        /\ (forall x, In x KS_apaY6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 33%nat) + 9)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 248).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaY6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaY6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaY6.kn0).
  { unfold know_ok, PapaY6.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaY6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaY6.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_50 / 8) + 2147450880) + 6) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 6) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapaY6.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaY6.ps0) with 0xae3fc in Hms. change (SR.ps_regs PapaY6.ps0) with (map (fun i => (i, nth i PapaY6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaY6.ps0) with PapaY6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaY6.regs0 PapaY6.regs_out0 80 KS_apaY6 KS_apaY6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaY6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaY6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaY6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY6.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PapaY6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY6.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PapaY6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY6.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PapaY6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaY6.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PapaY6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaC1 := LibSegBa_apaC1_b.
Definition KS_apaC1 : list nat := Eval vm_compute in (BG.kept_list 80 PapaC1.regs0 PapaC1.regs_out0).
Lemma KS_apaC1_ok : BG.kept_ok 80 PapaC1.regs0 PapaC1.regs_out0 KS_apaC1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaC1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 ((V 42%nat) - 40) -> getr R (reg 11) = Z_to_bv 64 (V 42%nat) -> getr R (reg 12) = Z_to_bv 64 0 -> getr R (reg 13) = Z_to_bv 64 ((((V 42%nat) - 40) / 8) + 2147450880) -> getr R (reg 14) = Z_to_bv 64 713520 -> getr R (reg 15) = Z_to_bv 64 4 -> getr R (reg 17) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 33%nat) + 392) ((V 42%nat) - 40) -> 4136 <= (V 42%nat) <= 140737488355328 -> aligned (V 42%nat) 8 ->
  L5.writable RSEGS M ((V 33%nat) + 400) 8 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 400) <= bv_unsigned a < ((V 33%nat) + 400) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 400) <= i < ((V 33%nat) + 400) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae330 M) (st fx' R' 0xab740 M')
        /\ (forall x, In x KS_apaC1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 713552
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 11) = Z_to_bv 64 40
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 400) (V 42%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G12 G13 G14 G15 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 K20 pvzI11 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI12 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K21l; move K21l before pvzI11; pose proof (proj2 pvzI11) as K21r; move K21r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K42l; move K42l before pvzI12; pose proof (proj2 pvzI12) as K42r; move K42r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 42%nat => vz_42 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaC1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaC1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaC1.kn0).
  { unfold know_ok, PapaC1.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K42l K42r) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear - HV42l HV42r K42l K42r) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K56]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaC1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaC1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 400) <= bv_unsigned a < (vz_33 + 400) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapaC1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaC1.ps0) with 0xab740 in Hms. change (SR.ps_regs PapaC1.ps0) with (map (fun i => (i, nth i PapaC1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaC1.ps0) with PapaC1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaC1.regs0 PapaC1.regs_out0 80 KS_apaC1 KS_apaC1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaC1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapaC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaC1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaC1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaC1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K42l K42r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaC2 := LibSegBa_apaC2_b.
Definition KS_apaC2 : list nat := Eval vm_compute in (BG.kept_list 80 PapaC2.regs0 PapaC2.regs_out0).
Lemma KS_apaC2_ok : BG.kept_ok 80 PapaC2.regs0 PapaC2.regs_out0 KS_apaC2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaC2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> 6905856 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 8 <= 2147446784) ->
  L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 256) + 256 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> ((V 50%nat) + 128 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 50%nat)) ->
  ((V 51%nat) + 1 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 51%nat)) -> L5.u64_at RSEGS M (V 34%nat) 1251456 -> L5KA.zeros_at M 2147607319 1 -> ((((V 34%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 34%nat) / 8) + 2147450880)) ->
  L5.writable RSEGS M ((V 33%nat) + 8) 2 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae350 M) (st fx' R' 0xae3fc M')
        /\ (forall x, In x KS_apaC2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 713640
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 692756
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 9) 1
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 pvzI11 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K41l; move K41l before pvzI11; pose proof (proj2 pvzI11) as K41r; move K41r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaC2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaC2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaC2.kn0).
  { unfold know_ok, PapaC2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K48) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K48) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K48) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K48; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K48; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K48; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K48) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K48) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K48) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K48) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51) | clear; lia | exact K42]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51; lia | clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51; lia | clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51; lia | clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51; lia | exactA K49]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear - HV34l HV34r K41l K41r K43 K45 K46 K47 K48 K51) | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K47 K51) | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K45) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K45; lia | exactA K63]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaC2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaC2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 2) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PapaC2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaC2.ps0) with 0xae3fc in Hms. change (SR.ps_regs PapaC2.ps0) with (map (fun i => (i, nth i PapaC2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaC2.ps0) with PapaC2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaC2.regs0 PapaC2.regs_out0 80 KS_apaC2 KS_apaC2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaC2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapaC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaC2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaC2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaC2.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PapaC2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K46) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaJ0 := LibSegBa_apaJ0_b.
Definition KS_apaJ0 : list nat := Eval vm_compute in (BG.kept_list 80 PapaJ0.regs0 PapaJ0.regs_out0).
Lemma KS_apaJ0_ok : BG.kept_ok 80 PapaJ0.regs0 PapaJ0.regs_out0 KS_apaJ0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaJ0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae15c M) (st fx' R' 0xae3fc M')
        /\ (forall x, In x KS_apaJ0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 33%nat) + 8)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaJ0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaJ0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaJ0.kn0).
  { unfold know_ok, PapaJ0.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaJ0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaJ0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaJ0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaJ0.ps0) with 0xae3fc in Hms. change (SR.ps_regs PapaJ0.ps0) with (map (fun i => (i, nth i PapaJ0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaJ0.ps0) with PapaJ0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaJ0.regs0 PapaJ0.regs_out0 80 KS_apaJ0 KS_apaJ0_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PapaJ0.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PapaJ0.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaJ4 := LibSegBa_apaJ4_b.
Definition KS_apaJ4 : list nat := Eval vm_compute in (BG.kept_list 80 PapaJ4.regs0 PapaJ4.regs_out0).
Lemma KS_apaJ4_ok : BG.kept_ok 80 PapaJ4.regs0 PapaJ4.regs_out0 KS_apaJ4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaJ4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae198 M) (st fx' R' 0xae3fc M')
        /\ (forall x, In x KS_apaJ4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 33%nat) + 8)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20 pvzI10 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K21l; move K21l before pvzI10; pose proof (proj2 pvzI10) as K21r; move K21r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaJ4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaJ4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaJ4.kn0).
  { unfold know_ok, PapaJ4.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaJ4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaJ4.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaJ4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaJ4.ps0) with 0xae3fc in Hms. change (SR.ps_regs PapaJ4.ps0) with (map (fun i => (i, nth i PapaJ4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaJ4.ps0) with PapaJ4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaJ4.regs0 PapaJ4.regs_out0 80 KS_apaJ4 KS_apaJ4_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PapaJ4.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PapaJ4.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaT0 := LibSegBa_apaT0_b.
Definition KS_apaT0 : list nat := Eval vm_compute in (BG.kept_list 80 PapaT0.regs0 PapaT0.regs_out0).
Lemma KS_apaT0_ok : BG.kept_ok 80 PapaT0.regs0 PapaT0.regs_out0 KS_apaT0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaT0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 17) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u8_at RSEGS M ((V 33%nat) + 9) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae3fc M) (st fx' R' 0xae0cc M')
        /\ (forall x, In x KS_apaT0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 2).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20 pvzI9 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV51l; move HV51l before pvzI5; pose proof (proj2 pvzI5) as HV51r; move HV51r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K21l; move K21l before pvzI9; pose proof (proj2 pvzI9) as K21r; move K21r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaT0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaT0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaT0.kn0).
  { unfold know_ok, PapaT0.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | byte_tac ltac:(clear) | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K36]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaT0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaT0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaT0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaT0.ps0) with 0xae0cc in Hms. change (SR.ps_regs PapaT0.ps0) with (map (fun i => (i, nth i PapaT0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaT0.ps0) with PapaT0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaT0.regs0 PapaT0.regs_out0 80 KS_apaT0 KS_apaT0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaT0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaT0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaT0.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaT1 := LibSegBa_apaT1_b.
Definition KS_apaT1 : list nat := Eval vm_compute in (BG.kept_list 80 PapaT1.regs0 PapaT1.regs_out0).
Lemma KS_apaT1_ok : BG.kept_ok 80 PapaT1.regs0 PapaT1.regs_out0 KS_apaT1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaT1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 17) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 392) -> getr R (reg 20) = Z_to_bv 64 40 -> getr R (reg 21) = Z_to_bv 64 143316 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) -> getr R (reg 27) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u8_at RSEGS M ((V 33%nat) + 9) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae3fc M) (st fx' R' 0xae510 M')
        /\ (forall x, In x KS_apaT1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 2).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 pvzI8 K15 K16 K17 K18 K19 K20 pvzI9 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV51l; move HV51l before pvzI5; pose proof (proj2 pvzI5) as HV51r; move HV51r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K14l; move K14l before pvzI8; pose proof (proj2 pvzI8) as K14r; move K14r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K21l; move K21l before pvzI9; pose proof (proj2 pvzI9) as K21r; move K21r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PapaT1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaT1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaT1.kn0).
  { unfold know_ok, PapaT1.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | byte_tac ltac:(clear) | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K36]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaT1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaT1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PapaT1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaT1.ps0) with 0xae510 in Hms. change (SR.ps_regs PapaT1.ps0) with (map (fun i => (i, nth i PapaT1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaT1.ps0) with PapaT1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaT1.regs0 PapaT1.regs_out0 80 KS_apaT1 KS_apaT1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaT1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaT1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PapaT1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaT1.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PapaX := LibSegBa_apaX_b.
Definition KS_apaX : list nat := Eval vm_compute in (BG.kept_list 80 PapaX.regs0 PapaX.regs_out0).
Lemma KS_apaX_ok : BG.kept_ok 80 PapaX.regs0 PapaX.regs_out0 KS_apaX = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaX_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 9) -> getr R (reg 25) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 26) = Z_to_bv 64 (V 33%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487424 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 9) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 256) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 256) + 256 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 256)) -> 6905856 <= (V 50%nat) <= 140737488355200 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 128 -> L5.writable RSEGS M (V 50%nat) 128 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 50%nat) + 120) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 128 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 128 <= ((V 2%nat) - 256)) -> (((V 2%nat) - 256) + 256 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 256)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 36%nat) -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((((V 33%nat) + 392) / 8) + 2147450880) ->
  aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 -> aligned (V 2%nat) 32 ->
  aligned (V 2%nat) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 216) (((V 34%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 50%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 50%nat) + 48) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((((V 33%nat) + 9) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae510 M) (st fx' R' 0xae5f4 M')
        /\ (forall x, In x KS_apaX -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 50%nat)
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
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450891) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450890) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450889) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450895) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450894) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450893) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450892) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.defined M' ((V 50%nat) + 8) 120).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G18 G22 G23 G24 G25 G26 K0 K1 K2 pvzI20 K4 K5 pvzI21 K7 K8 K9 K10 K11 K12 K13 pvzI22 K15 K16 K17 K18 K19 K20 pvzI23 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV60l; move HV60l before pvzI7; pose proof (proj2 pvzI7) as HV60r; move HV60r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV61l; move HV61l before pvzI8; pose proof (proj2 pvzI8) as HV61r; move HV61r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV62l; move HV62l before pvzI9; pose proof (proj2 pvzI9) as HV62r; move HV62r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV63l; move HV63l before pvzI10; pose proof (proj2 pvzI10) as HV63r; move HV63r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV69l; move HV69l before pvzI16; pose proof (proj2 pvzI16) as HV69r; move HV69r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV70l; move HV70l before pvzI17; pose proof (proj2 pvzI17) as HV70r; move HV70r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV71l; move HV71l before pvzI18; pose proof (proj2 pvzI18) as HV71r; move HV71r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV72l; move HV72l before pvzI19; pose proof (proj2 pvzI19) as HV72r; move HV72r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K6l; move K6l before pvzI21; pose proof (proj2 pvzI21) as K6r; move K6r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K14l; move K14l before pvzI22; pose proof (proj2 pvzI22) as K14r; move K14r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K21l; move K21l before pvzI23; pose proof (proj2 pvzI23) as K21r; move K21r before pvzI23; clear pvzI23.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PapaX.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaX.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaX.kn0).
  { unfold know_ok, PapaX.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K37]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K64]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PapaX.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaX.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PapaX.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaX.ps0) with 0xae5f4 in Hms. change (SR.ps_regs PapaX.ps0) with (map (fun i => (i, nth i PapaX.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaX.ps0) with PapaX.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaX.regs0 PapaX.regs_out0 80 KS_apaX KS_apaX_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaX.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PapaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

End PNAPAP.
