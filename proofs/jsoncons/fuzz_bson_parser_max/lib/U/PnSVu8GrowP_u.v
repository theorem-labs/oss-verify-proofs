(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_vgZ_u LibSegBs_vgZN_u LibSegBs_vgZ0_u LibSegBs_vgZL_u LibSegBs_vgF_u LibSegBs_vgFG_u LibSegBs_vgFN_u LibSegBs_vgG_u LibSegBs_vgP_u LibSegBs_vgC0_u LibSegBs_vgQ_u LibSegBs_vgQR_u LibSegBs_vgPN_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSVGP.
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
Module PvgZ := LibSegBs_vgZ_u.
Definition KS_vgZ_0 : list nat := Eval vm_compute in (BG.kept_list 60 PvgZ.regs0 PvgZ.regs_out0).
Lemma KS_vgZ_0_ok : BG.kept_ok 60 PvgZ.regs0 PvgZ.regs_out0 KS_vgZ_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vgZ_1 : list nat := Eval vm_compute in (BG.kept_list 60 PvgZ.regs0 PvgZ.regs_out1).
Lemma KS_vgZ_1_ok : BG.kept_ok 60 PvgZ.regs0 PvgZ.regs_out1 KS_vgZ_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vgZ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 43%nat) ->
  140735332483072 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 -> aligned (bv_unsigned (getr R (reg 10))) 8 ->
  L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + (V 35%nat)) ->
  4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 16 -> 0 <= (V 34%nat) <= 134217728 -> 1 <= (V 35%nat) <= 134217728 ->
  0 <= (V 43%nat) <= 134217728 -> 134217728 <= ((((-1) * (V 34%nat)) + (V 43%nat)) + 134217728) <= 268435456 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= i < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x396ac M) (st fx' R' 0x396fc M')
        /\ (forall x, In x KS_vgZ_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 34%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 34%nat)
        /\ (V 43%nat) <= (V 34%nat)
        /\ L5.u64_at RSEGS M' (bv_unsigned (getr R (reg 10))) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + (V 34%nat))
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + (V 35%nat)))
      \/ (msteps RSEGS (st fx R 0x396ac M) (st fx' R' 0x39704 M')
        /\ (forall x, In x KS_vgZ_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (((-1) * (V 34%nat)) + (V 43%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 34%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 34%nat)
        /\ (V 34%nat) < (V 43%nat)
        /\ L5.u64_at RSEGS M' (bv_unsigned (getr R (reg 10))) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + (V 34%nat))
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + (V 35%nat)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G11 pvzI6 K1 pvzI7 K3 K4 K5 K6 K7 pvzI8 K9 pvzI9 pvzI10 pvzI11 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K10l; move K10l before pvzI9; pose proof (proj2 pvzI9) as K10r; move K10r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K11l; move K11l before pvzI10; pose proof (proj2 pvzI10) as K11r; move K11r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K12l; move K12l before pvzI11; pose proof (proj2 pvzI11) as K12r; move K12r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K13l; move K13l before pvzI12; pose proof (proj2 pvzI12) as K13r; move K13r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PvgZ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvgZ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvgZ.kn0).
  { unfold know_ok, PvgZ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K2l K2r) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear) | clear - K2l K2r; lia | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r) | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r HV34l HV34r K10l K10r K13l K13r) | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r HV35l HV35r K11l K11r) | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K10l K10r K13l K13r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K12l K12r K13l K13r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K10l K10r K13l K13r HV43l HV43r K12l K12r) | exact (conj K13l K13r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvgZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvgZ.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvgZ.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K2l K2r) | evalEk' ZA Hag ltac:(clear) | clear - K2l K2r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvgZ.ps0) with 0x396fc in Hms. change (SR.ps_regs PvgZ.ps0) with (map (fun i => (i, nth i PvgZ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvgZ.ps0) with PvgZ.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgZ.regs0 PvgZ.regs_out0 60 KS_vgZ_0 KS_vgZ_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvgZ.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvgZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgZ.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgZ.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvgZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K2l K2r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K2l K2r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r HV34l HV34r K10l K10r K13l K13r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K2l K2r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r HV35l HV35r K11l K11r) | clear; lia]. 
  - right.
    change (SR.ps_pc PvgZ.ps1) with 0x39704 in Hms. change (SR.ps_regs PvgZ.ps1) with (map (fun i => (i, nth i PvgZ.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvgZ.ps1) with PvgZ.cells1 in Hcells. unfold PvgZ.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgZ.regs0 PvgZ.regs_out1 60 KS_vgZ_1 KS_vgZ_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvgZ.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvgZ.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgZ.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PvgZ.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgZ.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgZ.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgZ.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PvgZ.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K2l K2r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K2l K2r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r HV34l HV34r K10l K10r K13l K13r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K2l K2r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r HV35l HV35r K11l K11r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvgZN := LibSegBs_vgZN_u.
Definition KS_vgZN : list nat := Eval vm_compute in (BG.kept_list 60 PvgZN.regs0 PvgZN.regs_out0).
Lemma KS_vgZN_ok : BG.kept_ok 60 PvgZN.regs0 PvgZN.regs_out0 KS_vgZN = true. Proof. vm_compute. reflexivity. Qed.
Lemma vgZN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 43%nat) ->
  140735332483072 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 -> aligned (bv_unsigned (getr R (reg 10))) 8 ->
  L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) 0 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) 0 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) 0 ->
  1 <= (V 43%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x396ac M) (st fx' R' 0x39704 M')
        /\ (forall x, In x KS_vgZN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 G2 G11 pvzI3 K1 pvzI4 K3 K4 K5 K6 K7 pvzI5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV43l; move HV43l before pvzI2; pose proof (proj2 pvzI2) as HV43r; move HV43r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K2l; move K2l before pvzI4; pose proof (proj2 pvzI4) as K2r; move K2r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K8l; move K8l before pvzI5; pose proof (proj2 pvzI5) as K8r; move K8r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PvgZN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvgZN.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvgZN.kn0).
  { unfold know_ok, PvgZN.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K2l K2r) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear) | clear - K2l K2r; lia | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear) | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear) | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear) | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvgZN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvgZN.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvgZN.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvgZN.ps0) with 0x39704 in Hms. change (SR.ps_regs PvgZN.ps0) with (map (fun i => (i, nth i PvgZN.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvgZN.ps0) with PvgZN.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgZN.regs0 PvgZN.regs_out0 60 KS_vgZN KS_vgZN_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvgZN.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvgZN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgZN.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgZN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvgZN.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvgZN.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvgZ0 := LibSegBs_vgZ0_u.
Definition KS_vgZ0 : list nat := Eval vm_compute in (BG.kept_list 60 PvgZ0.regs0 PvgZ0.regs_out0).
Lemma KS_vgZ0_ok : BG.kept_ok 60 PvgZ0.regs0 PvgZ0.regs_out0 KS_vgZ0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vgZ0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 0 ->
  140735332483072 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 -> aligned (bv_unsigned (getr R (reg 10))) 8 ->
  L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) 0 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) 0 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x396ac M) (st fx' R' 0x396fc M')
        /\ (forall x, In x KS_vgZ0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0).
Proof.
  intros pvzI1 G2 G11 pvzI2 K1 pvzI3 K3 K4 K5 K6 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K0l; move K0l before pvzI2; pose proof (proj2 pvzI2) as K0r; move K0r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K2l; move K2l before pvzI3; pose proof (proj2 pvzI3) as K2r; move K2r before pvzI3; clear pvzI3.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PvgZ0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvgZ0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvgZ0.kn0).
  { unfold know_ok, PvgZ0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K2l K2r) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear) | clear - K2l K2r; lia | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear) | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear) | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear) | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvgZ0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvgZ0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvgZ0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvgZ0.ps0) with 0x396fc in Hms. change (SR.ps_regs PvgZ0.ps0) with (map (fun i => (i, nth i PvgZ0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvgZ0.ps0) with PvgZ0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgZ0.regs0 PvgZ0.regs_out0 60 KS_vgZ0 KS_vgZ0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvgZ0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvgZ0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgZ0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgZ0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvgZ0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvgZ0.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

Module PvgZL := LibSegBs_vgZL_u.
Definition KS_vgZL : list nat := Eval vm_compute in (BG.kept_list 60 PvgZL.regs0 PvgZL.regs_out0).
Lemma KS_vgZL_ok : BG.kept_ok 60 PvgZL.regs0 PvgZL.regs_out0 KS_vgZL = true. Proof. vm_compute. reflexivity. Qed.
Lemma vgZL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 43%nat) ->
  140735332483072 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 -> aligned (bv_unsigned (getr R (reg 10))) 8 ->
  L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + (V 35%nat)) ->
  4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 16 -> 0 <= (V 34%nat) <= 134217728 -> 1 <= (V 35%nat) <= 134217728 ->
  0 <= (V 43%nat) <= 134217728 -> 0 <= ((((-1) * (V 34%nat)) + (V 43%nat)) + 134217728) <= 134217727 -> ((((18446744073709551615 * (V 33%nat)) mod 2 ^ 64) + ((18446744073709551615 * (V 34%nat)) mod 2 ^ 64)) mod 2 ^ 64) < ((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + (V 43%nat)) mod 2 ^ 64) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= i < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x396ac M) (st fx' R' 0x396fc M')
        /\ (forall x, In x KS_vgZL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + (V 43%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (((-1) * (V 34%nat)) + (V 43%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (((-1) * (V 33%nat)) - (V 34%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 ((((-1) * (V 33%nat)) - (V 34%nat)) - 1)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + (V 43%nat))
        /\ L5.u64_at RSEGS M' (bv_unsigned (getr R (reg 10))) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + (V 35%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G11 pvzI6 K1 pvzI7 K3 K4 K5 K6 K7 pvzI8 K9 pvzI9 pvzI10 pvzI11 pvzI12 K14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K2l; move K2l before pvzI7; pose proof (proj2 pvzI7) as K2r; move K2r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K10l; move K10l before pvzI9; pose proof (proj2 pvzI9) as K10r; move K10r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K11l; move K11l before pvzI10; pose proof (proj2 pvzI10) as K11r; move K11r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K12l; move K12l before pvzI11; pose proof (proj2 pvzI11) as K12r; move K12r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K13l; move K13l before pvzI12; pose proof (proj2 pvzI12) as K13r; move K13r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PvgZL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvgZL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvgZL.kn0).
  { unfold know_ok, PvgZL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K2l K2r) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear) | clear - K2l K2r; lia | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K14) | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K14 HV34l HV34r K10l K10r K13l K13r) | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K2l K2r) | evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K14 HV35l HV35r K11l K11r) | clear - K2l K2r; lia | clear - K2l K2r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K14) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K8l K8r K14) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K10l K10r K13l K13r K14) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K12l K12r K13l K13r K14) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K10l K10r K13l K13r K14 HV43l HV43r K12l K12r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | generalize K14; clear; intro; destruct (Z.ltb_spec0 ((((18446744073709551615 * vz_33) mod 2 ^ 64) + ((18446744073709551615 * vz_34) mod 2 ^ 64)) mod 2 ^ 64) ((((18446744073709551615 * vz_34) mod 2 ^ 64) + vz_43) mod 2 ^ 64)); lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvgZL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvgZL.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvgZL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K2l K2r) | evalEk' ZA Hag ltac:(clear) | clear - K2l K2r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvgZL.ps0) with 0x396fc in Hms. change (SR.ps_regs PvgZL.ps0) with (map (fun i => (i, nth i PvgZL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvgZL.ps0) with PvgZL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgZL.regs0 PvgZL.regs_out0 60 KS_vgZL KS_vgZL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvgZL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvgZL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgZL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvgZL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgZL.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgZL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgZL.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvgZL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K2l K2r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K14 HV43l HV43r K12l K12r K13l K13r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K2l K2r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K14) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K2l K2r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K8l K8r K14 HV35l HV35r K11l K11r) | clear; lia]. 
Qed.

(* [comment removed for export] *)
Module PvgF := LibSegBs_vgF_u.
Definition KS_vgF_0 : list nat := Eval vm_compute in (BG.kept_list 60 PvgF.regs0 PvgF.regs_out0).
Lemma KS_vgF_0_ok : BG.kept_ok 60 PvgF.regs0 PvgF.regs_out0 KS_vgF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vgF_1 : list nat := Eval vm_compute in (BG.kept_list 60 PvgF.regs0 PvgF.regs_out1).
Lemma KS_vgF_1_ok : BG.kept_ok 60 PvgF.regs0 PvgF.regs_out1 KS_vgF_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vgF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 43%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 96) + 96 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 96)) -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + (V 35%nat)) -> 4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 16 ->
  0 <= (V 34%nat) <= 134217728 -> 1 <= (V 35%nat) <= 134217728 -> 1 <= (V 43%nat) <= 134217728 -> L5.writable RSEGS M ((V 33%nat) + (V 34%nat)) (V 43%nat) ->
  (((V 33%nat) + (V 34%nat)) + (V 43%nat) <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 33%nat) + (V 34%nat))) -> (((V 33%nat) + (V 34%nat)) + (V 43%nat) <= ((V 2%nat) - 96) \/ ((V 2%nat) - 96) + 96 <= ((V 33%nat) + (V 34%nat))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> ~ ((((V 33%nat) + (V 34%nat)) + 0) <= bv_unsigned a < (((V 33%nat) + (V 34%nat)) + 0) + (V 43%nat)) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= i < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> ~ ((((V 33%nat) + (V 34%nat)) + 0) <= i < (((V 33%nat) + (V 34%nat)) + 0) + (V 43%nat)) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x39704 M) (st fx' R' 0x39818 M')
        /\ (forall x, In x KS_vgF_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + ((V 34%nat) + (V 43%nat)))
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + ((V 34%nat) + (V 43%nat)))
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + ((V 34%nat) + (V 43%nat)))
        /\ (V 43%nat) <= ((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + (V 35%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' (bv_unsigned (getr R (reg 10))) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + (V 35%nat)))
      \/ (msteps RSEGS (st fx R 0x39704 M) (st fx' R' 0x3972c M')
        /\ (forall x, In x KS_vgF_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 34%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (((-1) * (V 34%nat)) + (V 35%nat))
        /\ ((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + (V 35%nat)) mod 2 ^ 64) < (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' (bv_unsigned (getr R (reg 10))) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + (V 34%nat))
        /\ L5.u64_at RSEGS M' ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + (V 35%nat)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G11 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 K8 K9 pvzI8 K11 pvzI9 pvzI10 pvzI11 K15 K16 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K10l; move K10l before pvzI8; pose proof (proj2 pvzI8) as K10r; move K10r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K13l; move K13l before pvzI10; pose proof (proj2 pvzI10) as K13r; move K13r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PvgF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvgF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvgF.kn0).
  { unfold know_ok, PvgF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K17; lia | clear - HV2l HV2r K0l K0r K6 K17; lia | clear - HV2l HV2r K0l K0r K6 K17; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6 K16) | evalEk ZA ltac:(clear) | clear - K3l K3r K6 K16; lia | clear - K3l K3r K6 K16; lia | clear - K3l K3r K6 K16; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6 K16) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K16) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K16 K17) | clear - K3l K3r K6 K16; lia | clear - K3l K3r K6 K16; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K16) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K16 K17 HV34l HV34r K12l K12r) | clear - K3l K3r K6 K16; lia | clear - K3l K3r K6 K16; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6 K16) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K16 K17 HV35l HV35r K13l K13r) | clear - K3l K3r K6 K16; lia | clear - K3l K3r K6 K16; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K16 K17) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K16 K17) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K16 K17) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K14l K14r K16 K17) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K16 K17 HV34l HV34r K12l K12r) | evalEk ZA ltac:(clear - HV43l HV43r K14l K14r K16 K17) | clear - HV33l HV33r K10l K10r K16 K17 HV34l HV34r K12l K12r HV43l HV43r K14l K14r; lia | clear - HV33l HV33r K10l K10r K16 K17 HV34l HV34r K12l K12r HV43l HV43r K14l K14r; lia | clear - HV33l HV33r K10l K10r K16 K17 HV34l HV34r K12l K12r HV43l HV43r K14l K14r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K16 K17 HV34l HV34r K12l K12r) | evalEk ZA ltac:(clear - HV43l HV43r K14l K14r K16 K17) | evalEk ZA ltac:(clear - K3l K3r K6 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r K16 K17 HV34l HV34r K12l K12r) | evalEk ZA ltac:(clear - HV43l HV43r K14l K14r K16 K17) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvgF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvgF.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> ~ (((bv_unsigned (getr R (reg 10))) + 0) <= bv_unsigned a < ((bv_unsigned (getr R (reg 10))) + 0) + 24) -> ~ (((vz_33 + vz_34) + 0) <= bv_unsigned a < ((vz_33 + vz_34) + 0) + vz_43) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PvgF.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - K3l K3r K6 K16) | evalEk' ZA Hag ltac:(clear) | clear - K3l K3r K6 K16 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K16 K17 HV34l HV34r K12l K12r) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K14l K14r K16 K17) | clear - HV33l HV33r K10l K10r K16 K17 HV34l HV34r K12l K12r HV43l HV43r K14l K14r Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvgF.ps0) with 0x39818 in Hms. change (SR.ps_regs PvgF.ps0) with (map (fun i => (i, nth i PvgF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvgF.ps0) with PvgF.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgF.regs0 PvgF.regs_out0 60 KS_vgF_0 KS_vgF_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvgF.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvgF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgF.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvgF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgF.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgF.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvgF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgF.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvgF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K16) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K16 K17 HV34l HV34r K12l K12r HV43l HV43r K14l K14r) | clear; lia]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K16) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K16 K17) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K16) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K16 K17 HV35l HV35r K13l K13r) | clear; lia]. 
  - right.
    change (SR.ps_pc PvgF.ps1) with 0x3972c in Hms. change (SR.ps_regs PvgF.ps1) with (map (fun i => (i, nth i PvgF.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvgF.ps1) with PvgF.cells1 in Hcells. unfold PvgF.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgF.regs0 PvgF.regs_out1 60 KS_vgF_1 KS_vgF_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvgF.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PvgF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgF.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PvgF.regs_out1]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PvgF.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PvgF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgF.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PvgF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgF.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PvgF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgF.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K16) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K16 K17) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K16) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K16 K17 HV34l HV34r K12l K12r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - K3l K3r K6 K16) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K10l K10r K16 K17 HV35l HV35r K13l K13r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvgFG := LibSegBs_vgFG_u.
Definition KS_vgFG : list nat := Eval vm_compute in (BG.kept_list 60 PvgFG.regs0 PvgFG.regs_out0).
Lemma KS_vgFG_ok : BG.kept_ok 60 PvgFG.regs0 PvgFG.regs_out0 KS_vgFG = true. Proof. vm_compute. reflexivity. Qed.
Lemma vgFG_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 43%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 96) + 96 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 96)) -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) (V 33%nat) ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) ((V 33%nat) + (V 35%nat)) -> 4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 16 ->
  0 <= (V 34%nat) <= 134217728 -> 1 <= (V 35%nat) <= 134217728 -> 1 <= (V 43%nat) <= 134217728 -> ((((18446744073709551615 * (V 34%nat)) mod 2 ^ 64) + (V 35%nat)) mod 2 ^ 64) < (V 43%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39704 M) (st fx' R' 0x3972c M')
        /\ (forall x, In x KS_vgFG -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + (V 35%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 34%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (((-1) * (V 34%nat)) + (V 35%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G11 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 K8 K9 pvzI8 K11 pvzI9 pvzI10 pvzI11 K15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K10l; move K10l before pvzI8; pose proof (proj2 pvzI8) as K10r; move K10r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K13l; move K13l before pvzI10; pose proof (proj2 pvzI10) as K13r; move K13r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PvgFG.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvgFG.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvgFG.kn0).
  { unfold know_ok, PvgFG.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r HV34l HV34r K12l K12r K15) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r HV35l HV35r K13l K13r K15) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K15) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K13l K13r K15) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K14l K14r K15) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | generalize K15; clear; intro; destruct (Z.ltb_spec0 ((((18446744073709551615 * vz_34) mod 2 ^ 64) + vz_35) mod 2 ^ 64) vz_43); lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvgFG.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvgFG.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvgFG.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvgFG.ps0) with 0x3972c in Hms. change (SR.ps_regs PvgFG.ps0) with (map (fun i => (i, nth i PvgFG.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvgFG.ps0) with PvgFG.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgFG.regs0 PvgFG.regs_out0 60 KS_vgFG KS_vgFG_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvgFG.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvgFG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgFG.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvgFG.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PvgFG.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvgFG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgFG.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvgFG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgFG.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvgFG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgFG.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgFG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvgFN := LibSegBs_vgFN_u.
Definition KS_vgFN : list nat := Eval vm_compute in (BG.kept_list 60 PvgFN.regs0 PvgFN.regs_out0).
Lemma KS_vgFN_ok : BG.kept_ok 60 PvgFN.regs0 PvgFN.regs_out0 KS_vgFN = true. Proof. vm_compute. reflexivity. Qed.
Lemma vgFN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 43%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 140735332483072 <= (bv_unsigned (getr R (reg 10))) <= 140737488355304 ->
  aligned (bv_unsigned (getr R (reg 10))) 8 -> L5.writable RSEGS M (bv_unsigned (getr R (reg 10))) 24 -> (((V 2%nat) - 96) + 96 <= (bv_unsigned (getr R (reg 10))) \/ (bv_unsigned (getr R (reg 10))) + 24 <= ((V 2%nat) - 96)) -> L5.u64_at RSEGS M (bv_unsigned (getr R (reg 10))) 0 ->
  L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 8) 0 -> L5.u64_at RSEGS M ((bv_unsigned (getr R (reg 10))) + 16) 0 -> 1 <= (V 43%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39704 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_vgFN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 235604
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = getr R (reg 10)
        /\ getr R' (reg 14) = Z_to_bv 64 4611686018427387903
        /\ getr R' (reg 18) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 10)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 10)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 235368
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 G2 G11 pvzI3 K1 K2 pvzI4 K4 K5 K6 K7 K8 K9 pvzI5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV43l; move HV43l before pvzI2; pose proof (proj2 pvzI2) as HV43r; move HV43r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K10l; move K10l before pvzI5; pose proof (proj2 pvzI5) as K10r; move K10r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PvgFN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvgFN.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvgFN.kn0).
  { unfold know_ok, PvgFN.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - K3l K3r K6) | evalEk ZA ltac:(clear) | clear - K3l K3r K6; lia | clear - K3l K3r K6; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvgFN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvgFN.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvgFN.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvgFN.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PvgFN.ps0) with (map (fun i => (i, nth i PvgFN.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvgFN.ps0) with PvgFN.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgFN.regs0 PvgFN.regs_out0 60 KS_vgFN KS_vgFN_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvgFN.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvgFN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgFN.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvgFN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgFN.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvgFN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgFN.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvgFN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgFN.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvgFN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgFN.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvgFN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgFN.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgFN.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PvgFN.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvgFN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgFN.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvgFN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - K3l K3r K6) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K10l K10r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - K3l K3r K6) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvgG := LibSegBs_vgG_u.
Definition KS_vgG_0 : list nat := Eval vm_compute in (BG.kept_list 60 PvgG.regs0 PvgG.regs_out0).
Lemma KS_vgG_0_ok : BG.kept_ok 60 PvgG.regs0 PvgG.regs_out0 KS_vgG_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vgG_1 : list nat := Eval vm_compute in (BG.kept_list 60 PvgG.regs0 PvgG.regs_out1).
Lemma KS_vgG_1_ok : BG.kept_ok 60 PvgG.regs0 PvgG.regs_out1 KS_vgG_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vgG_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 33%nat) + (V 35%nat)) -> getr R (reg 12) = Z_to_bv 64 ((V 33%nat) + (V 34%nat)) -> getr R (reg 13) = Z_to_bv 64 (((-1) * (V 34%nat)) + (V 35%nat)) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 96)) -> L5.u64_at RSEGS M (V 10%nat) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((V 10%nat) + 16) ((V 33%nat) + (V 35%nat)) -> 4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 16 ->
  0 <= (V 34%nat) <= 134217728 -> 1 <= (V 35%nat) <= 134217728 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> 1 <= (V 43%nat) <= 134217728 -> 1 <= ((V 34%nat) + (V 43%nat)) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x3972c M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_vgG_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 235604
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 9) = Z_to_bv 64 (2 * (V 35%nat))
        /\ getr R' (reg 10) = Z_to_bv 64 (2 * (V 35%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (2 * (V 35%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 4611686018427387903
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 235368
        /\ (((V 34%nat) + (V 43%nat)) mod 2 ^ 64) < ((2 * (V 35%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 46%nat))
      \/ (msteps RSEGS (st fx R 0x3972c M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_vgG_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 235604
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 34%nat) + (V 43%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 4611686018427387903
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 235368
        /\ ((2 * (V 35%nat)) mod 2 ^ 64) <= (((V 34%nat) + (V 43%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 46%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G12 G13 pvzI10 K1 K2 pvzI11 K4 K5 K6 K7 K8 K9 pvzI12 K11 pvzI13 pvzI14 K14 K15 K16 pvzI15 pvzI16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K0l; move K0l before pvzI10; pose proof (proj2 pvzI10) as K0r; move K0r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K10l; move K10l before pvzI12; pose proof (proj2 pvzI12) as K10r; move K10r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K12l; move K12l before pvzI13; pose proof (proj2 pvzI13) as K12r; move K12r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K13l; move K13l before pvzI14; pose proof (proj2 pvzI14) as K13r; move K13r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K17l; move K17l before pvzI15; pose proof (proj2 pvzI15) as K17r; move K17r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K18l; move K18l before pvzI16; pose proof (proj2 pvzI16) as K18r; move K18r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 47%nat. }
  assert (HR: regs_ok E PvgG.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvgG.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvgG.kn0).
  { unfold know_ok, PvgG.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r HV34l HV34r K12l K12r K18l K18r) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear - HV33l HV33r K10l K10r HV35l HV35r K13l K13r) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K10l K10r) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K18l K18r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K17l K17r K18l K18r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K18l K18r HV43l HV43r K17l K17r) | exact (conj K18l K18r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvgG.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvgG.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvgG.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvgG.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PvgG.ps0) with (map (fun i => (i, nth i PvgG.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvgG.ps0) with PvgG.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgG.regs0 PvgG.regs_out0 60 KS_vgG_0 KS_vgG_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvgG.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvgG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvgG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvgG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvgG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvgG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvgG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvgG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvgG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvgG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K17l K17r K18l K18r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. 
  - right.
    change (SR.ps_pc PvgG.ps1) with 0xb03b8 in Hms. change (SR.ps_regs PvgG.ps1) with (map (fun i => (i, nth i PvgG.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvgG.ps1) with PvgG.cells1 in Hcells. unfold PvgG.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgG.regs0 PvgG.regs_out1 60 KS_vgG_1 KS_vgG_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvgG.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PvgG.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PvgG.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PvgG.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PvgG.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PvgG.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvgG.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PvgG.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgG.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PvgG.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgG.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PvgG.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K17l K17r K18l K18r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvgP := LibSegBs_vgP_u.
Definition KS_vgP_0 : list nat := Eval vm_compute in (BG.kept_list 60 PvgP.regs0 PvgP.regs_out0).
Lemma KS_vgP_0_ok : BG.kept_ok 60 PvgP.regs0 PvgP.regs_out0 KS_vgP_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vgP_1 : list nat := Eval vm_compute in (BG.kept_list 60 PvgP.regs0 PvgP.regs_out1).
Lemma KS_vgP_1_ok : BG.kept_ok 60 PvgP.regs0 PvgP.regs_out1 KS_vgP_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vgP_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 9) = Z_to_bv 64 (V 38%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 96)) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  0 <= (V 34%nat) <= 134217728 -> 1 <= (V 35%nat) <= 134217728 -> 1 <= (V 43%nat) <= 134217728 -> 1 <= (V 38%nat) <= 134217728 ->
  4096 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 16 -> 0 <= (((-1) * (V 34%nat)) + ((V 38%nat) - (V 43%nat))) <= 134217728 -> L5.writable RSEGS M (V 37%nat) (V 38%nat) ->
  ((V 37%nat) + (V 38%nat) <= (V 10%nat) \/ (V 10%nat) + 24 <= (V 37%nat)) -> ((V 37%nat) + (V 38%nat) <= ((V 2%nat) - 96) \/ ((V 2%nat) - 96) + 96 <= (V 37%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 10%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) 235368 ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 10%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 47%nat) -> L5.u64_at RSEGS M (V 10%nat) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((V 10%nat) + 16) ((V 33%nat) + (V 35%nat)) -> L5.writable RSEGS M ((V 34%nat) + (V 37%nat)) (V 43%nat) -> (((V 34%nat) + (V 37%nat)) + (V 43%nat) <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 34%nat) + (V 37%nat))) ->
  (((V 34%nat) + (V 37%nat)) + (V 43%nat) <= ((V 2%nat) - 96) \/ ((V 2%nat) - 96) + 96 <= ((V 34%nat) + (V 37%nat))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> ~ ((((V 34%nat) + (V 37%nat)) + 0) <= bv_unsigned a < (((V 34%nat) + (V 37%nat)) + 0) + (V 43%nat)) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> ~ ((((V 34%nat) + (V 37%nat)) + 0) <= i < (((V 34%nat) + (V 37%nat)) + 0) + (V 43%nat)) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x39854 M) (st fx' R' 0xab480 M')
        /\ (forall x, In x KS_vgP_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 235876
        /\ getr R' (reg 9) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + (V 37%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 34%nat) + (V 37%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 235392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) ((V 34%nat) + ((V 37%nat) + (V 43%nat)))
        /\ 0 <= (V 34%nat) <= 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 37%nat) + (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 34%nat) + (V 37%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 10%nat))
      \/ (msteps RSEGS (st fx R 0x39854 M) (st fx' R' 0xab480 M')
        /\ (forall x, In x KS_vgP_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 235876
        /\ getr R' (reg 9) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 235392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) ((V 34%nat) + ((V 37%nat) + (V 43%nat)))
        /\ 1 <= (V 34%nat) <= 134217728
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 37%nat) + (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 34%nat) + (V 37%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 10%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G10 G18 pvzI13 K1 K2 pvzI14 K4 K5 K6 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 K13 pvzI21 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K0l; move K0l before pvzI13; pose proof (proj2 pvzI13) as K0r; move K0r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K7l; move K7l before pvzI15; pose proof (proj2 pvzI15) as K7r; move K7r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K8l; move K8l before pvzI16; pose proof (proj2 pvzI16) as K8r; move K8r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K9l; move K9l before pvzI17; pose proof (proj2 pvzI17) as K9r; move K9r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K10l; move K10l before pvzI18; pose proof (proj2 pvzI18) as K10r; move K10r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K11l; move K11l before pvzI19; pose proof (proj2 pvzI19) as K11r; move K11r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K12l; move K12l before pvzI20; pose proof (proj2 pvzI20) as K12r; move K12r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K14l; move K14l before pvzI21; pose proof (proj2 pvzI21) as K14r; move K14r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 37%nat => vz_37 | 38%nat => vz_38 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PvgP.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvgP.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvgP.kn0).
  { unfold know_ok, PvgP.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16 K31) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16 K31) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16 K31) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K16 K31; lia | clear - HV10l HV10r K3l K3r K6 K16 K31; lia | clear - HV10l HV10r K3l K3r K6 K16 K31; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16 K31) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K14l K14r K31 K32) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K10l K10r K14l K14r K31 K32) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K14l K14r K16 K17) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K16 K17 K31 K32) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K16 K17 K31 K32) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K14l K14r K31 K32 HV38l HV38r K11l K11r K16 K17 HV43l HV43r K10l K10r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K16 K17 K31 K32) | evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K14l K14r K16 K17) | clear - HV37l HV37r K12l K12r K16 K17 K31 K32 HV38l HV38r K11l K11r K14l K14r; lia | clear - HV37l HV37r K12l K12r K16 K17 K31 K32 HV38l HV38r K11l K11r K14l K14r; lia | clear - HV37l HV37r K12l K12r K16 K17 K31 K32 HV38l HV38r K11l K11r K14l K14r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K16 K17 K31 K32) | evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K14l K14r K16 K17) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16 K31) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K16 K17 K31 K32) | evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K14l K14r K16 K17) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16 K31) | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16 K31) | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk ZA ltac:(clear - HV43l HV43r K10l K10r K14l K14r K31 K32) | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | clear - HV2l HV2r K0l K0r K6 K17 K32; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16 K31) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r) | clear - HV10l HV10r K3l K3r K6 K16 K31; lia | clear - HV10l HV10r K3l K3r K6 K16 K31; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16 K31) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r HV34l HV34r K8l K8r K14l K14r K31 K32) | clear - HV10l HV10r K3l K3r K6 K16 K31; lia | clear - HV10l HV10r K3l K3r K6 K16 K31; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16 K31) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r HV35l HV35r K9l K9r) | clear - HV10l HV10r K3l K3r K6 K16 K31; lia | clear - HV10l HV10r K3l K3r K6 K16 K31; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K14l K14r K31 K32 HV37l HV37r K12l K12r K16 K17) | evalEk ZA ltac:(clear - HV43l HV43r K10l K10r K14l K14r K31 K32) | clear - HV34l HV34r K8l K8r K14l K14r K31 K32 HV37l HV37r K12l K12r K16 K17 HV43l HV43r K10l K10r; lia | clear - HV34l HV34r K8l K8r K14l K14r K31 K32 HV37l HV37r K12l K12r K16 K17 HV43l HV43r K10l K10r; lia | clear - HV34l HV34r K8l K8r K14l K14r K31 K32 HV37l HV37r K12l K12r K16 K17 HV43l HV43r K10l K10r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K14l K14r K31 K32 HV37l HV37r K12l K12r K16 K17) | evalEk ZA ltac:(clear - HV43l HV43r K10l K10r K14l K14r K31 K32) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K16 K31) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K14l K14r K31 K32 HV37l HV37r K12l K12r K16 K17) | evalEk ZA ltac:(clear - HV43l HV43r K10l K10r K14l K14r K31 K32) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvgP.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvgP.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> ~ (((vz_34 + vz_37) + 0) <= bv_unsigned a < ((vz_34 + vz_37) + 0) + vz_43) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PvgP.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K17 K32 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K8l K8r K14l K14r K31 K32 HV37l HV37r K12l K12r K16 K17) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K10l K10r K14l K14r K31 K32) | clear - HV34l HV34r K8l K8r K14l K14r K31 K32 HV37l HV37r K12l K12r K16 K17 HV43l HV43r K10l K10r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvgP.ps0) with 0xab480 in Hms. change (SR.ps_regs PvgP.ps0) with (map (fun i => (i, nth i PvgP.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvgP.ps0) with PvgP.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgP.regs0 PvgP.regs_out0 60 KS_vgP_0 KS_vgP_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvgP.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvgP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgP.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvgP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgP.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvgP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgP.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvgP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgP.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvgP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgP.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgP.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvgP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgP.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvgP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgP.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvgP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K10l K10r K14l K14r K31 K32) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K16 K31) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K8l K8r K14l K14r K31 K32 HV37l HV37r K12l K12r K16 K17 HV43l HV43r K10l K10r) | clear; lia]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K8l K8r K14l K14r K31 K32)]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r K16 K17 K31 K32 HV38l HV38r K11l K11r K14l K14r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K8l K8r K14l K14r K31 K32 HV37l HV37r K12l K12r K16 K17) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r K16 K17 K31 K32) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K16 K31) | clear; lia]. 
  - right.
    change (SR.ps_pc PvgP.ps1) with 0xab480 in Hms. change (SR.ps_regs PvgP.ps1) with (map (fun i => (i, nth i PvgP.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvgP.ps1) with PvgP.cells1 in Hcells. unfold PvgP.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgP.regs0 PvgP.regs_out1 60 KS_vgP_1 KS_vgP_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvgP.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PvgP.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgP.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PvgP.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgP.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvgP.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgP.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PvgP.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgP.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgP.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgP.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PvgP.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgP.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PvgP.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvgP.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PvgP.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K10l K10r K14l K14r K31 K32) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K16 K31) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K8l K8r K14l K14r K31 K32 HV37l HV37r K12l K12r K16 K17 HV43l HV43r K10l K10r) | clear; lia]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K8l K8r K14l K14r K31 K32)]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r K16 K17 K31 K32 HV38l HV38r K11l K11r K14l K14r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K8l K8r K14l K14r K31 K32 HV37l HV37r K12l K12r K16 K17) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r K16 K17 K31 K32) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K17 K32) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K16 K31) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvgC0 := LibSegBs_vgC0_u.
Definition KS_vgC0 : list nat := Eval vm_compute in (BG.kept_list 60 PvgC0.regs0 PvgC0.regs_out0).
Lemma KS_vgC0_ok : BG.kept_ok 60 PvgC0.regs0 PvgC0.regs_out0 KS_vgC0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vgC0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 235876 -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 0 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> 4096 <= (V 33%nat) <= 140737488355328 -> aligned (V 33%nat) 16 ->
  4096 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xab480 M) (st fx' R' 0x39964 M')
        /\ (forall x, In x KS_vgC0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 G1 G2 G10 G11 G12 pvzI4 K1 pvzI5 K3 pvzI6 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K2l; move K2l before pvzI5; pose proof (proj2 pvzI5) as K2r; move K2r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K4l; move K4l before pvzI6; pose proof (proj2 pvzI6) as K4r; move K4r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PvgC0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvgC0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvgC0.kn0).
  { unfold know_ok, PvgC0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K2l K2r) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K4l K4r) | clear; lia | exact K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvgC0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvgC0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvgC0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvgC0.ps0) with 0x39964 in Hms. change (SR.ps_regs PvgC0.ps0) with (map (fun i => (i, nth i PvgC0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvgC0.ps0) with PvgC0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgC0.regs0 PvgC0.regs_out0 60 KS_vgC0 KS_vgC0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvgC0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgC0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgC0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvgC0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvgC0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvgC0.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvgQ := LibSegBs_vgQ_u.
Definition KS_vgQ : list nat := Eval vm_compute in (BG.kept_list 60 PvgQ.regs0 PvgQ.regs_out0).
Lemma KS_vgQ_ok : BG.kept_ok 60 PvgQ.regs0 PvgQ.regs_out0 KS_vgQ = true. Proof. vm_compute. reflexivity. Qed.
Lemma vgQ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 9) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 18) = Z_to_bv 64 (V 37%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 96)) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  0 <= (V 34%nat) <= 134217728 -> 1 <= (V 35%nat) <= 134217728 -> 1 <= (V 43%nat) <= 134217728 -> 1 <= (V 38%nat) <= 134217728 ->
  4096 <= (V 37%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 10%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) ((V 37%nat) + (V 38%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 48) ((V 34%nat) + ((V 37%nat) + (V 43%nat))) -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 34%nat) + (V 37%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) 235392 -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 10%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) (V 47%nat) -> L5.u64_at RSEGS M (V 10%nat) (V 33%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 8) ((V 33%nat) + (V 34%nat)) -> L5.u64_at RSEGS M ((V 10%nat) + 16) ((V 33%nat) + (V 35%nat)) ->
  aligned (V 37%nat) 16 -> 0 <= (((-1) * (V 34%nat)) + ((V 38%nat) - (V 43%nat))) <= 134217728 -> L5.writable RSEGS M (V 37%nat) (V 38%nat) -> ((V 37%nat) + (V 38%nat) <= (V 10%nat) \/ (V 10%nat) + 24 <= (V 37%nat)) ->
  ((V 37%nat) + (V 38%nat) <= ((V 2%nat) - 96) \/ ((V 2%nat) - 96) + 96 <= (V 37%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> ~ (((V 10%nat) + 0) <= bv_unsigned a < ((V 10%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> ~ (((V 10%nat) + 0) <= i < ((V 10%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39964 M) (st fx' R' 0x56720 M')
        /\ (forall x, In x KS_vgQ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 235400
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 33%nat) + (V 35%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 16) ((V 37%nat) + (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) ((V 34%nat) + ((V 37%nat) + (V 43%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 33%nat)
        /\ L5.u64_at RSEGS M' (V 10%nat) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 235392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 47%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G18 pvzI14 K1 K2 pvzI15 K4 K5 K6 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 pvzI22 K30 K31 K32.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV54l; move HV54l before pvzI13; pose proof (proj2 pvzI13) as HV54r; move HV54r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K3l; move K3l before pvzI15; pose proof (proj2 pvzI15) as K3r; move K3r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K7l; move K7l before pvzI16; pose proof (proj2 pvzI16) as K7r; move K7r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K8l; move K8l before pvzI17; pose proof (proj2 pvzI17) as K8r; move K8r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K9l; move K9l before pvzI18; pose proof (proj2 pvzI18) as K9r; move K9r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K10l; move K10l before pvzI19; pose proof (proj2 pvzI19) as K10r; move K10r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K11l; move K11l before pvzI20; pose proof (proj2 pvzI20) as K11r; move K11r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K12l; move K12l before pvzI21; pose proof (proj2 pvzI21) as K12r; move K12r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K29l; move K29l before pvzI22; pose proof (proj2 pvzI22) as K29r; move K29r before pvzI22; clear pvzI22.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_54 := V 54%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 54%nat => Z_to_bv 64 vz_54 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 37%nat => vz_37 | 38%nat => vz_38 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 54%nat => vz_54 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PvgQ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvgQ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvgQ.kn0).
  { unfold know_ok, PvgQ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K32; lia | clear - HV2l HV2r K0l K0r K6 K32; lia | clear - HV2l HV2r K0l K0r K6 K32; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K31) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K31) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K31) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K31; lia | clear - HV10l HV10r K3l K3r K6 K31; lia | clear - HV10l HV10r K3l K3r K6 K31; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K31) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K29l K29r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K10l K10r K29l K29r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K29l K29r K31 K32) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K31 K32) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6 K32; lia | clear - HV2l HV2r K0l K0r K6 K32; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6 K32; lia | clear - HV2l HV2r K0l K0r K6 K32; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6 K32; lia | clear - HV2l HV2r K0l K0r K6 K32; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K31) | clear - HV2l HV2r K0l K0r K6 K32; lia | clear - HV2l HV2r K0l K0r K6 K32; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K31 K32 HV38l HV38r K11l K11r K29l K29r) | clear - HV2l HV2r K0l K0r K6 K32; lia | clear - HV2l HV2r K0l K0r K6 K32; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K29l K29r HV37l HV37r K12l K12r K31 K32 HV43l HV43r K10l K10r) | clear - HV2l HV2r K0l K0r K6 K32; lia | clear - HV2l HV2r K0l K0r K6 K32; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K29l K29r HV37l HV37r K12l K12r K31 K32) | clear - HV2l HV2r K0l K0r K6 K32; lia | clear - HV2l HV2r K0l K0r K6 K32; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K31 K32) | clear - HV2l HV2r K0l K0r K6 K32; lia | clear - HV2l HV2r K0l K0r K6 K32; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K32; lia | clear - HV2l HV2r K0l K0r K6 K32; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K31) | clear - HV2l HV2r K0l K0r K6 K32; lia | clear - HV2l HV2r K0l K0r K6 K32; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk ZA ltac:(clear - HV43l HV43r K10l K10r K29l K29r) | clear - HV2l HV2r K0l K0r K6 K32; lia | clear - HV2l HV2r K0l K0r K6 K32; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K6 K32; lia | clear - HV2l HV2r K0l K0r K6 K32; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K31) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r) | clear - HV10l HV10r K3l K3r K6 K31; lia | clear - HV10l HV10r K3l K3r K6 K31; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K31) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r HV34l HV34r K8l K8r K29l K29r) | clear - HV10l HV10r K3l K3r K6 K31; lia | clear - HV10l HV10r K3l K3r K6 K31; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K31) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r HV35l HV35r K9l K9r) | clear - HV10l HV10r K3l K3r K6 K31; lia | clear - HV10l HV10r K3l K3r K6 K31; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K31 K32) | clear; lia | exact K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K8l K8r K29l K29r HV38l HV38r K11l K11r K31 K32 HV43l HV43r K10l K10r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K31 K32) | evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K29l K29r K31 K32) | clear - HV37l HV37r K12l K12r K31 K32 HV38l HV38r K11l K11r K29l K29r; lia | clear - HV37l HV37r K12l K12r K31 K32 HV38l HV38r K11l K11r K29l K29r; lia | clear - HV37l HV37r K12l K12r K31 K32 HV38l HV38r K11l K11r K29l K29r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K31 K32) | evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K29l K29r K31 K32) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K31) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K31 K32) | evalEk ZA ltac:(clear - HV38l HV38r K11l K11r K29l K29r K31 K32) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvgQ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvgQ.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> ~ ((vz_10 + 0) <= bv_unsigned a < (vz_10 + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PvgQ.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K32 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K31) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K31 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvgQ.ps0) with 0x56720 in Hms. change (SR.ps_regs PvgQ.ps0) with (map (fun i => (i, nth i PvgQ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvgQ.ps0) with PvgQ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgQ.regs0 PvgQ.regs_out0 60 KS_vgQ KS_vgQ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvgQ.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvgQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgQ.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvgQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgQ.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvgQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgQ.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvgQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgQ.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvgQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgQ.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvgQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgQ.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvgQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgQ.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgQ.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvgQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r HV35l HV35r K9l K9r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K31) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r K31 K32 HV38l HV38r K11l K11r K29l K29r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K31) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K8l K8r K29l K29r HV37l HV37r K12l K12r K31 K32 HV43l HV43r K10l K10r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K31) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r K31 K32) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K31) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K31) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K10l K10r K29l K29r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K32) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

Module PvgQR := LibSegBs_vgQR_u.
Definition KS_vgQR : list nat := Eval vm_compute in (BG.kept_list 60 PvgQR.regs0 PvgQR.regs_out0).
Lemma KS_vgQR_ok : BG.kept_ok 60 PvgQR.regs0 PvgQR.regs_out0 KS_vgQR = true. Proof. vm_compute. reflexivity. Qed.
Lemma vgQR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 96)) -> 4096 <= (V 33%nat) <= 140737488355328 ->
  0 <= (V 34%nat) <= 134217728 -> 1 <= (V 35%nat) <= 134217728 -> 1 <= (V 43%nat) <= 134217728 -> 1 <= (V 38%nat) <= 134217728 ->
  4096 <= (V 37%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39788 M) (st fx' R' 0x39798 M')
        /\ (forall x, In x KS_vgQR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 46%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G18 pvzI14 K1 K2 pvzI15 K4 K5 K6 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 K13 K14 K15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV54l; move HV54l before pvzI13; pose proof (proj2 pvzI13) as HV54r; move HV54r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K3l; move K3l before pvzI15; pose proof (proj2 pvzI15) as K3r; move K3r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K7l; move K7l before pvzI16; pose proof (proj2 pvzI16) as K7r; move K7r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K8l; move K8l before pvzI17; pose proof (proj2 pvzI17) as K8r; move K8r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K9l; move K9l before pvzI18; pose proof (proj2 pvzI18) as K9r; move K9r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K10l; move K10l before pvzI19; pose proof (proj2 pvzI19) as K10r; move K10r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K11l; move K11l before pvzI20; pose proof (proj2 pvzI20) as K11r; move K11r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K12l; move K12l before pvzI21; pose proof (proj2 pvzI21) as K12r; move K12r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_54 := V 54%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 54%nat => Z_to_bv 64 vz_54 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 37%nat => vz_37 | 38%nat => vz_38 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 54%nat => vz_54 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PvgQR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvgQR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvgQR.kn0).
  { unfold know_ok, PvgQR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | clear - HV10l HV10r K3l K3r K6; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6; lia | clear - HV2l HV2r K0l K0r K6; lia | exactA K15]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvgQR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvgQR.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvgQR.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvgQR.ps0) with 0x39798 in Hms. change (SR.ps_regs PvgQR.ps0) with (map (fun i => (i, nth i PvgQR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvgQR.ps0) with PvgQR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgQR.regs0 PvgQR.regs_out0 60 KS_vgQR KS_vgQR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvgQR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvgQR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgQR.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvgQR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgQR.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvgQR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgQR.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvgQR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. 
Qed.

(* [comment removed for export] *)
Module PvgPN := LibSegBs_vgPN_u.
Definition KS_vgPN : list nat := Eval vm_compute in (BG.kept_list 60 PvgPN.regs0 PvgPN.regs_out0).
Lemma KS_vgPN_ok : BG.kept_ok 60 PvgPN.regs0 PvgPN.regs_out0 KS_vgPN = true. Proof. vm_compute. reflexivity. Qed.
Lemma vgPN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 0 ->
  140735332483152 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 96) 96 -> 140735332483072 <= (V 10%nat) <= 140737488355304 ->
  aligned (V 10%nat) 8 -> L5.writable RSEGS M (V 10%nat) 24 -> (((V 2%nat) - 96) + 96 <= (V 10%nat) \/ (V 10%nat) + 24 <= ((V 2%nat) - 96)) -> 1 <= (V 43%nat) <= 134217728 ->
  4096 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 16 -> L5.writable RSEGS M (V 37%nat) (V 43%nat) -> ((V 37%nat) + (V 43%nat) <= (V 10%nat) \/ (V 10%nat) + 24 <= (V 37%nat)) ->
  ((V 37%nat) + (V 43%nat) <= ((V 2%nat) - 96) \/ ((V 2%nat) - 96) + 96 <= (V 37%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 10%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) 235368 -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 10%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 47%nat) -> L5.u64_at RSEGS M (V 10%nat) 0 -> L5.u64_at RSEGS M ((V 10%nat) + 8) 0 ->
  L5.u64_at RSEGS M ((V 10%nat) + 16) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 96) -> ~ (((V 10%nat) + 0) <= bv_unsigned a < ((V 10%nat) + 0) + 24) -> ~ (((V 37%nat) + 0) <= bv_unsigned a < ((V 37%nat) + 0) + (V 43%nat)) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 96) -> ~ (((V 10%nat) + 0) <= i < ((V 10%nat) + 0) + 24) -> ~ (((V 37%nat) + 0) <= i < ((V 37%nat) + 0) + (V 43%nat)) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39854 M) (st fx' R' 0x39798 M')
        /\ (forall x, In x KS_vgPN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) 0
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 16) ((V 37%nat) + (V 43%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 0
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 8) ((V 37%nat) + (V 43%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 0
        /\ L5.u64_at RSEGS M' (V 10%nat) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 235392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 10%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G18 pvzI9 K1 K2 pvzI10 K4 K5 K6 pvzI11 pvzI12 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV47l; move HV47l before pvzI8; pose proof (proj2 pvzI8) as HV47r; move HV47r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K0l; move K0l before pvzI9; pose proof (proj2 pvzI9) as K0r; move K0r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K7l; move K7l before pvzI11; pose proof (proj2 pvzI11) as K7r; move K7r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K8l; move K8l before pvzI12; pose proof (proj2 pvzI12) as K8r; move K8r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 37%nat => Z_to_bv 64 vz_37 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 37%nat => vz_37 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PvgPN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvgPN.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvgPN.kn0).
  { unfold know_ok, PvgPN.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K12; lia | clear - HV2l HV2r K0l K0r K6 K12; lia | clear - HV2l HV2r K0l K0r K6 K12; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K11; lia | clear - HV10l HV10r K3l K3r K6 K11; lia | clear - HV10l HV10r K3l K3r K6 K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K11) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K7l K7r K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K8l K8r K11 K12) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K8l K8r K11 K12) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K8l K8r K11 K12) | evalEk ZA ltac:(clear - HV43l HV43r K7l K7r K11 K12) | clear - HV37l HV37r K8l K8r K11 K12 HV43l HV43r K7l K7r; lia | clear - HV37l HV37r K8l K8r K11 K12 HV43l HV43r K7l K7r; lia | clear - HV37l HV37r K8l K8r K11 K12 HV43l HV43r K7l K7r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K8l K8r K11 K12) | evalEk ZA ltac:(clear - HV43l HV43r K7l K7r K11 K12) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K8l K8r K11 K12) | evalEk ZA ltac:(clear - HV43l HV43r K7l K7r K11 K12) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K6 K12; lia | clear - HV2l HV2r K0l K0r K6 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K6 K12; lia | clear - HV2l HV2r K0l K0r K6 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K6 K12; lia | clear - HV2l HV2r K0l K0r K6 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K11) | clear - HV2l HV2r K0l K0r K6 K12; lia | clear - HV2l HV2r K0l K0r K6 K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K12; lia | clear - HV2l HV2r K0l K0r K6 K12; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K12; lia | clear - HV2l HV2r K0l K0r K6 K12; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K11) | clear - HV2l HV2r K0l K0r K6 K12; lia | clear - HV2l HV2r K0l K0r K6 K12; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear - HV43l HV43r K7l K7r K11 K12) | clear - HV2l HV2r K0l K0r K6 K12; lia | clear - HV2l HV2r K0l K0r K6 K12; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K6 K12; lia | clear - HV2l HV2r K0l K0r K6 K12; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K11; lia | clear - HV10l HV10r K3l K3r K6 K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K11; lia | clear - HV10l HV10r K3l K3r K6 K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K3l K3r K6 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K11; lia | clear - HV10l HV10r K3l K3r K6 K11; lia | exactA K24]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvgPN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvgPN.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 96) -> ~ ((vz_10 + 0) <= bv_unsigned a < (vz_10 + 0) + 24) -> ~ ((vz_37 + 0) <= bv_unsigned a < (vz_37 + 0) + vz_43) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PvgPN.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K6 K12 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K3l K3r K6 K11 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K8l K8r K11 K12) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K7l K7r K11 K12) | clear - HV37l HV37r K8l K8r K11 K12 HV43l HV43r K7l K7r Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvgPN.ps0) with 0x39798 in Hms. change (SR.ps_regs PvgPN.ps0) with (map (fun i => (i, nth i PvgPN.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvgPN.ps0) with PvgPN.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvgPN.regs0 PvgPN.regs_out0 60 KS_vgPN KS_vgPN_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvgPN.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvgPN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgPN.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvgPN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgPN.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvgPN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgPN.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvgPN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgPN.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvgPN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgPN.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvgPN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgPN.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvgPN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgPN.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvgPN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgPN.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvgPN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgPN.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvgPN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvgPN.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvgPN.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K11) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K8l K8r K11 K12 HV43l HV43r K7l K7r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K11) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K8l K8r K11 K12 HV43l HV43r K7l K7r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K11) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K8l K8r K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K7l K7r K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K11) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K6 K12) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K3l K3r K6 K11) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PNSVGP.
