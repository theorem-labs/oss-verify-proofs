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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_tsA_u LibSegBs_tsH1_u LibSegBs_tsH0_u LibSegBs_tsRS_u LibSegBs_tsRL_u LibSegBs_tsQS_u LibSegBs_tsQL_u LibSegBs_tsE_u LibSegBs_tsF_u LibSegBs_tsDS_u LibSegBs_tsDL_u LibSegBs_tsD2_u LibSegBs_tsD3_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMSSRP.
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
Module PtsA := LibSegBs_tsA_u.
Definition KS_tsA_0 : list nat := Eval vm_compute in (BG.kept_list 56 PtsA.regs0 PtsA.regs_out0).
Lemma KS_tsA_0_ok : BG.kept_ok 56 PtsA.regs0 PtsA.regs_out0 KS_tsA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsA_1 : list nat := Eval vm_compute in (BG.kept_list 56 PtsA.regs0 PtsA.regs_out1).
Lemma KS_tsA_1_ok : BG.kept_ok 56 PtsA.regs0 PtsA.regs_out1 KS_tsA_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tsA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 0 <= (V 35%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x39398 M) (st fx' R' 0x393d8 M')
        /\ (forall x, In x KS_tsA_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 34%nat) + 1)
        /\ 1 <= (((V 35%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x39398 M) (st fx' R' 0x39520 M')
        /\ (forall x, In x KS_tsA_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ (((V 35%nat) - 0) mod 2 ^ 64) < 1
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
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G10 G11 G12 pvzI5 K1 K2 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PtsA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtsA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtsA.kn0).
  { unfold know_ok, PtsA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtsA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtsA.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 80) <= bv_unsigned a < (vz_2 - 80) + 80) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtsA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PtsA.ps0) with 0x393d8 in Hms. change (SR.ps_regs PtsA.ps0) with (map (fun i => (i, nth i PtsA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtsA.ps0) with PtsA.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsA.regs0 PtsA.regs_out0 56 KS_tsA_0 KS_tsA_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtsA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PtsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PtsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PtsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PtsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PtsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsA.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PtsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  - right.
    change (SR.ps_pc PtsA.ps1) with 0x39520 in Hms. change (SR.ps_regs PtsA.ps1) with (map (fun i => (i, nth i PtsA.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtsA.ps1) with PtsA.cells1 in Hcells. unfold PtsA.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsA.regs0 PtsA.regs_out1 56 KS_tsA_1 KS_tsA_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtsA.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsH1 := LibSegBs_tsH1_u.
Definition KS_tsH1_0 : list nat := Eval vm_compute in (BG.kept_list 56 PtsH1.regs0 PtsH1.regs_out0).
Lemma KS_tsH1_0_ok : BG.kept_ok 56 PtsH1.regs0 PtsH1.regs_out0 KS_tsH1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsH1_1 : list nat := Eval vm_compute in (BG.kept_list 56 PtsH1.regs0 PtsH1.regs_out1).
Lemma KS_tsH1_1_ok : BG.kept_ok 56 PtsH1.regs0 PtsH1.regs_out1 KS_tsH1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tsH1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 34%nat) + 1) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 33%nat) <= 140737488355032 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 33%nat) \/ (V 33%nat) + 296 <= ((V 2%nat) - 80)) -> L5.u64_at RSEGS M ((V 33%nat) + 288) (V 37%nat) -> 1 <= (V 37%nat) <= 16384 ->
  L5.u64_at RSEGS M ((V 33%nat) + 272) 16384 -> 1 <= (V 36%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x393d8 M) (st fx' R' 0x39404 M')
        /\ (forall x, In x KS_tsH1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234464
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ (V 36%nat) < 16384)
      \/ (msteps RSEGS (st fx R 0x393d8 M) (st fx' R' 0x39404 M')
        /\ (forall x, In x KS_tsH1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234464
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 16384
        /\ 16384 <= (V 36%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G21 G22 pvzI7 K1 K2 pvzI8 K4 K5 K6 pvzI9 K8 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K9l; move K9l before pvzI10; pose proof (proj2 pvzI10) as K9r; move K9r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PtsH1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtsH1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtsH1.kn0).
  { unfold know_ok, PtsH1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtsH1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtsH1.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtsH1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PtsH1.ps0) with 0x39404 in Hms. change (SR.ps_regs PtsH1.ps0) with (map (fun i => (i, nth i PtsH1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtsH1.ps0) with PtsH1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsH1.regs0 PtsH1.regs_out0 56 KS_tsH1_0 KS_tsH1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtsH1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtsH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PtsH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PtsH1.ps1) with 0x39404 in Hms. change (SR.ps_regs PtsH1.ps1) with (map (fun i => (i, nth i PtsH1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtsH1.ps1) with PtsH1.cells1 in Hcells. unfold PtsH1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsH1.regs0 PtsH1.regs_out1 56 KS_tsH1_1 KS_tsH1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtsH1.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsH1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH1.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsH1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PtsH1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH1.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PtsH1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsH0 := LibSegBs_tsH0_u.
Definition KS_tsH0_0 : list nat := Eval vm_compute in (BG.kept_list 56 PtsH0.regs0 PtsH0.regs_out0).
Lemma KS_tsH0_0_ok : BG.kept_ok 56 PtsH0.regs0 PtsH0.regs_out0 KS_tsH0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsH0_1 : list nat := Eval vm_compute in (BG.kept_list 56 PtsH0.regs0 PtsH0.regs_out1).
Lemma KS_tsH0_1_ok : BG.kept_ok 56 PtsH0.regs0 PtsH0.regs_out1 KS_tsH0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsH0_2 : list nat := Eval vm_compute in (BG.kept_list 56 PtsH0.regs0 PtsH0.regs_out2).
Lemma KS_tsH0_2_ok : BG.kept_ok 56 PtsH0.regs0 PtsH0.regs_out2 KS_tsH0_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tsH0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 34%nat) + 1) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> 140735332483072 <= (V 33%nat) <= 140737488355032 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 33%nat) \/ (V 33%nat) + 296 <= ((V 2%nat) - 80)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M ((V 33%nat) + 288) 0 ->
  L5.u64_at RSEGS M ((V 33%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 33%nat) + 240) (V 38%nat) -> 140735332483072 <= (V 38%nat) <= 140737488355056 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 80) + 80 <= (V 38%nat) \/ (V 38%nat) + 272 <= ((V 2%nat) - 80)) -> L5.u64_at RSEGS M (V 38%nat) 740792 -> L5.u8_at RSEGS M ((V 38%nat) + 152) (V 52%nat) -> 0 <= (V 52%nat) <= 2 ->
  1 <= (V 36%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 54%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x393d8 M) (st fx' R' 0x39404 M')
        /\ (forall x, In x KS_tsH0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234464
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ (V 36%nat) < 16384
        /\ (((((4611686018427387904 * (V 52%nat)) mod 2 ^ 64) / 9223372036854775808) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x393d8 M) (st fx' R' 0x39470 M')
        /\ (forall x, In x KS_tsH0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234464
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 16384
        /\ 16384 <= (V 36%nat)
        /\ (((((4611686018427387904 * (V 52%nat)) mod 2 ^ 64) / 9223372036854775808) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x393d8 M) (st fx' R' 0x39520 M')
        /\ (forall x, In x KS_tsH0_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 35%nat) - (V 36%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 54%nat)
        /\ 1 <= (((((4611686018427387904 * (V 52%nat)) mod 2 ^ 64) / 9223372036854775808) - 0) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G8 G9 G18 G21 G22 pvzI17 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 pvzI18 K12 K13 K14 K15 K16 K17 pvzI19 K19 K20 K21 K22 pvzI20 pvzI21 K25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV49l; move HV49l before pvzI12; pose proof (proj2 pvzI12) as HV49r; move HV49r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV50l; move HV50l before pvzI13; pose proof (proj2 pvzI13) as HV50r; move HV50r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV51l; move HV51l before pvzI14; pose proof (proj2 pvzI14) as HV51r; move HV51r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV52l; move HV52l before pvzI15; pose proof (proj2 pvzI15) as HV52r; move HV52r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV54l; move HV54l before pvzI16; pose proof (proj2 pvzI16) as HV54r; move HV54r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K0l; move K0l before pvzI17; pose proof (proj2 pvzI17) as K0r; move K0r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K11l; move K11l before pvzI18; pose proof (proj2 pvzI18) as K11r; move K11r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K18l; move K18l before pvzI19; pose proof (proj2 pvzI19) as K18r; move K18r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K23l; move K23l before pvzI20; pose proof (proj2 pvzI20) as K23r; move K23r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K24l; move K24l before pvzI21; pose proof (proj2 pvzI21) as K24r; move K24r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_54 := V 54%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 54%nat => Z_to_bv 64 vz_54 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 38%nat => vz_38 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 54%nat => vz_54 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PtsH0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtsH0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtsH0.kn0).
  { unfold know_ok, PtsH0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K20) | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K20) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K20) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K20) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K18l K18r K20; lia | clear - HV38l HV38r K18l K18r K20; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K20) | evalEk ZA ltac:(clear - HV52l HV52r K23l K23r) | clear - HV38l HV38r K18l K18r K20; lia | clear - HV38l HV38r K18l K18r K20; lia | byte_tac ltac:(clear - HV52l HV52r K23l K23r) | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K25]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtsH0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtsH0.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtsH0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PtsH0.ps0) with 0x39404 in Hms. change (SR.ps_regs PtsH0.ps0) with (map (fun i => (i, nth i PtsH0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtsH0.ps0) with PtsH0.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsH0.regs0 PtsH0.regs_out0 56 KS_tsH0_0 KS_tsH0_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtsH0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PtsH0.ps1) with 0x39470 in Hms. change (SR.ps_regs PtsH0.ps1) with (map (fun i => (i, nth i PtsH0.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtsH0.ps1) with PtsH0.cells1 in Hcells. unfold PtsH0.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsH0.regs0 PtsH0.regs_out1 56 KS_tsH0_1 KS_tsH0_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtsH0.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. 
    change (SR.ps_pc PtsH0.ps2) with 0x39520 in Hms. change (SR.ps_regs PtsH0.ps2) with (map (fun i => (i, nth i PtsH0.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtsH0.ps2) with PtsH0.cells2 in Hcells. unfold PtsH0.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsH0.regs0 PtsH0.regs_out2 56 KS_tsH0_2 KS_tsH0_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtsH0.regs_out2 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out2 E' R' 2 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out2 E' R' 8 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out2 E' R' 9 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out2 E' R' 19 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out2 E' R' 20 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out2 E' R' 22 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsH0.regs_out2 E' R' 23 Hregs) by (clear; lia). cbn [nth PtsH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsRS := LibSegBs_tsRS_u.
Definition KS_tsRS : list nat := Eval vm_compute in (BG.kept_list 56 PtsRS.regs0 PtsRS.regs_out0).
Lemma KS_tsRS_ok : BG.kept_ok 56 PtsRS.regs0 PtsRS.regs_out0 KS_tsRS = true. Proof. vm_compute. reflexivity. Qed.
Lemma tsRS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 42%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 34%nat) + 1) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 80)) -> L5.u8_at RSEGS M (V 34%nat) (V 39%nat) -> 0 <= (V 39%nat) <= 44 ->
  Z.testbit (V 39%nat) 0 = false -> 1 <= (V 42%nat) <= 16384 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39404 M) (st fx' R' 0x59000 M')
        /\ (forall x, In x KS_tsRS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234540
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + ((V 39%nat) / 2))
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 39%nat) / 2)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G18 G19 G21 G22 pvzI8 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV42l; move HV42l before pvzI7; pose proof (proj2 pvzI7) as HV42r; move HV42r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K9l; move K9l before pvzI11; pose proof (proj2 pvzI11) as K9r; move K9r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 39%nat => Z_to_bv 64 vz_39 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 39%nat => vz_39 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PtsRS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtsRS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtsRS.kn0).
  { unfold know_ok, PtsRS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | byte_tac ltac:(clear - HV39l HV39r K7l K7r K8) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_false vz_39 ltac:(clear - HV39l HV39r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtsRS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtsRS.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtsRS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtsRS.ps0) with 0x59000 in Hms. change (SR.ps_regs PtsRS.ps0) with (map (fun i => (i, nth i PtsRS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtsRS.ps0) with PtsRS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsRS.regs0 PtsRS.regs_out0 56 KS_tsRS KS_tsRS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtsRS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsRS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsRS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsRS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsRS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtsRS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsRS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtsRS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtsRS.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PtsRS.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsRL := LibSegBs_tsRL_u.
Definition KS_tsRL : list nat := Eval vm_compute in (BG.kept_list 56 PtsRL.regs0 PtsRL.regs_out0).
Lemma KS_tsRL_ok : BG.kept_ok 56 PtsRL.regs0 PtsRL.regs_out0 KS_tsRL = true. Proof. vm_compute. reflexivity. Qed.
Lemma tsRL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 42%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 34%nat) + 1) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 80)) -> L5.u8_at RSEGS M (V 34%nat) (V 39%nat) -> 0 <= (V 39%nat) <= 255 ->
  Z.testbit (V 39%nat) 0 = true -> L5.u64_at RSEGS M ((V 34%nat) + 8) (V 40%nat) -> 0 <= (V 40%nat) <= 134217728 -> 1 <= (V 42%nat) <= 16384 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39404 M) (st fx' R' 0x59000 M')
        /\ (forall x, In x KS_tsRL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234540
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + (V 42%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G18 G19 G21 G22 pvzI9 K1 K2 pvzI10 K4 K5 K6 pvzI11 K8 K9 pvzI12 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV42l; move HV42l before pvzI8; pose proof (proj2 pvzI8) as HV42r; move HV42r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K0l; move K0l before pvzI9; pose proof (proj2 pvzI9) as K0r; move K0r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K7l; move K7l before pvzI11; pose proof (proj2 pvzI11) as K7r; move K7r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K10l; move K10l before pvzI12; pose proof (proj2 pvzI12) as K10r; move K10r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K11l; move K11l before pvzI13; pose proof (proj2 pvzI13) as K11r; move K11r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 39%nat => vz_39 | 40%nat => vz_40 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PtsRL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtsRL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtsRL.kn0).
  { unfold know_ok, PtsRL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | byte_tac ltac:(clear - HV39l HV39r K7l K7r K8) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_true vz_39 ltac:(clear - HV39l HV39r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV40l HV40r K10l K10r) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtsRL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtsRL.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtsRL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtsRL.ps0) with 0x59000 in Hms. change (SR.ps_regs PtsRL.ps0) with (map (fun i => (i, nth i PtsRL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtsRL.ps0) with PtsRL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsRL.regs0 PtsRL.regs_out0 56 KS_tsRL KS_tsRL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtsRL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsRL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsRL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsRL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsRL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtsRL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsRL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtsRL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtsRL.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PtsRL.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsQS := LibSegBs_tsQS_u.
Definition KS_tsQS : list nat := Eval vm_compute in (BG.kept_list 56 PtsQS.regs0 PtsQS.regs_out0).
Lemma KS_tsQS_ok : BG.kept_ok 56 PtsQS.regs0 PtsQS.regs_out0 KS_tsQS = true. Proof. vm_compute. reflexivity. Qed.
Lemma tsQS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 42%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 34%nat) + 1) -> getr R (reg 23) = Z_to_bv 64 (V 43%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 80)) -> L5.u8_at RSEGS M (V 34%nat) (V 39%nat) -> 0 <= (V 39%nat) <= 44 ->
  Z.testbit (V 39%nat) 0 = false -> 1 <= (V 42%nat) <= 16384 -> 0 <= (V 43%nat) <= 22 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3942c M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_tsQS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234588
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 34%nat) + (V 43%nat)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 42%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G18 G19 G21 G22 G23 pvzI9 K1 K2 pvzI10 K4 K5 K6 pvzI11 K8 pvzI12 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV42l; move HV42l before pvzI7; pose proof (proj2 pvzI7) as HV42r; move HV42r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K0l; move K0l before pvzI9; pose proof (proj2 pvzI9) as K0r; move K0r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K7l; move K7l before pvzI11; pose proof (proj2 pvzI11) as K7r; move K7r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K9l; move K9l before pvzI12; pose proof (proj2 pvzI12) as K9r; move K9r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K10l; move K10l before pvzI13; pose proof (proj2 pvzI13) as K10r; move K10r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 39%nat => Z_to_bv 64 vz_39 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 39%nat => vz_39 | 42%nat => vz_42 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PtsQS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtsQS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtsQS.kn0).
  { unfold know_ok, PtsQS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | byte_tac ltac:(clear - HV39l HV39r K7l K7r K8) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_false vz_39 ltac:(clear - HV39l HV39r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtsQS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtsQS.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtsQS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtsQS.ps0) with 0x370d0 in Hms. change (SR.ps_regs PtsQS.ps0) with (map (fun i => (i, nth i PtsQS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtsQS.ps0) with PtsQS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsQS.regs0 PtsQS.regs_out0 56 KS_tsQS KS_tsQS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtsQS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsQS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsQS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsQS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsQS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtsQS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtsQS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtsQS.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsQL := LibSegBs_tsQL_u.
Definition KS_tsQL : list nat := Eval vm_compute in (BG.kept_list 56 PtsQL.regs0 PtsQL.regs_out0).
Lemma KS_tsQL_ok : BG.kept_ok 56 PtsQL.regs0 PtsQL.regs_out0 KS_tsQL = true. Proof. vm_compute. reflexivity. Qed.
Lemma tsQL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 42%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 34%nat) + 1) -> getr R (reg 23) = Z_to_bv 64 (V 43%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 80)) -> L5.u8_at RSEGS M (V 34%nat) (V 39%nat) -> 0 <= (V 39%nat) <= 255 ->
  Z.testbit (V 39%nat) 0 = true -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355328 -> 1 <= (V 42%nat) <= 16384 ->
  0 <= (V 43%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3942c M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_tsQL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234588
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 41%nat) + (V 43%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 42%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G18 G19 G21 G22 G23 pvzI10 K1 K2 pvzI11 K4 K5 K6 pvzI12 K8 K9 pvzI13 pvzI14 pvzI15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV42l; move HV42l before pvzI8; pose proof (proj2 pvzI8) as HV42r; move HV42r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV43l; move HV43l before pvzI9; pose proof (proj2 pvzI9) as HV43r; move HV43r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K0l; move K0l before pvzI10; pose proof (proj2 pvzI10) as K0r; move K0r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K10l; move K10l before pvzI13; pose proof (proj2 pvzI13) as K10r; move K10r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K11l; move K11l before pvzI14; pose proof (proj2 pvzI14) as K11r; move K11r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 39%nat => vz_39 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PtsQL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtsQL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtsQL.kn0).
  { unfold know_ok, PtsQL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | byte_tac ltac:(clear - HV39l HV39r K7l K7r K8) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_true vz_39 ltac:(clear - HV39l HV39r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtsQL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtsQL.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtsQL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtsQL.ps0) with 0x370d0 in Hms. change (SR.ps_regs PtsQL.ps0) with (map (fun i => (i, nth i PtsQL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtsQL.ps0) with PtsQL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsQL.regs0 PtsQL.regs_out0 56 KS_tsQL KS_tsQL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtsQL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsQL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsQL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsQL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsQL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtsQL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtsQL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtsQL.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsE := LibSegBs_tsE_u.
Definition KS_tsE_0 : list nat := Eval vm_compute in (BG.kept_list 56 PtsE.regs0 PtsE.regs_out0).
Lemma KS_tsE_0_ok : BG.kept_ok 56 PtsE.regs0 PtsE.regs_out0 KS_tsE_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsE_1 : list nat := Eval vm_compute in (BG.kept_list 56 PtsE.regs0 PtsE.regs_out1).
Lemma KS_tsE_1_ok : BG.kept_ok 56 PtsE.regs0 PtsE.regs_out1 KS_tsE_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsE_2 : list nat := Eval vm_compute in (BG.kept_list 56 PtsE.regs0 PtsE.regs_out2).
Lemma KS_tsE_2_ok : BG.kept_ok 56 PtsE.regs0 PtsE.regs_out2 KS_tsE_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tsE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 53%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 42%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 34%nat) + 1) -> getr R (reg 23) = Z_to_bv 64 (V 43%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> 0 <= (V 53%nat) <= 16384 ->
  1 <= (V 42%nat) <= 16384 -> 0 <= (V 43%nat) <= 134217728 -> 1 <= (V 36%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 54%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x3945c M) (st fx' R' 0x59000 M')
        /\ (forall x, In x KS_tsE_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234732
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 43%nat) + (V 53%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ 1 <= (((V 53%nat) - (V 42%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x3945c M) (st fx' R' 0x393d8 M')
        /\ (forall x, In x KS_tsE_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) - (V 53%nat))
        /\ 1 <= (((((V 36%nat) + ((18446744073709551615 * (V 53%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64)
        /\ (((V 53%nat) - (V 42%nat)) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x3945c M) (st fx' R' 0x39520 M')
        /\ (forall x, In x KS_tsE_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 35%nat) + (((-1) * (V 36%nat)) + (V 53%nat)))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 54%nat)
        /\ (((((V 36%nat) + ((18446744073709551615 * (V 53%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ (((V 53%nat) - (V 42%nat)) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G10 G18 G19 G21 G22 G23 pvzI18 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 pvzI19 pvzI20 pvzI21 pvzI22 K15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV44l; move HV44l before pvzI8; pose proof (proj2 pvzI8) as HV44r; move HV44r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV45l; move HV45l before pvzI9; pose proof (proj2 pvzI9) as HV45r; move HV45r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV46l; move HV46l before pvzI10; pose proof (proj2 pvzI10) as HV46r; move HV46r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV47l; move HV47l before pvzI11; pose proof (proj2 pvzI11) as HV47r; move HV47r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV48l; move HV48l before pvzI12; pose proof (proj2 pvzI12) as HV48r; move HV48r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV49l; move HV49l before pvzI13; pose proof (proj2 pvzI13) as HV49r; move HV49r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV50l; move HV50l before pvzI14; pose proof (proj2 pvzI14) as HV50r; move HV50r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV51l; move HV51l before pvzI15; pose proof (proj2 pvzI15) as HV51r; move HV51r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV53l; move HV53l before pvzI16; pose proof (proj2 pvzI16) as HV53r; move HV53r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV54l; move HV54l before pvzI17; pose proof (proj2 pvzI17) as HV54r; move HV54r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K11l; move K11l before pvzI19; pose proof (proj2 pvzI19) as K11r; move K11r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K12l; move K12l before pvzI20; pose proof (proj2 pvzI20) as K12r; move K12r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K13l; move K13l before pvzI21; pose proof (proj2 pvzI21) as K13r; move K13r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K14l; move K14l before pvzI22; pose proof (proj2 pvzI22) as K14r; move K14r before pvzI22; clear pvzI22.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 53%nat => vz_53 | 54%nat => vz_54 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PtsE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtsE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtsE.kn0).
  { unfold know_ok, PtsE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K15]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtsE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtsE.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtsE.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PtsE.ps0) with 0x59000 in Hms. change (SR.ps_regs PtsE.ps0) with (map (fun i => (i, nth i PtsE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtsE.ps0) with PtsE.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsE.regs0 PtsE.regs_out0 56 KS_tsE_0 KS_tsE_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtsE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsE.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsE.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsE.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PtsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PtsE.ps1) with 0x393d8 in Hms. change (SR.ps_regs PtsE.ps1) with (map (fun i => (i, nth i PtsE.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtsE.ps1) with PtsE.cells1 in Hcells. unfold PtsE.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsE.regs0 PtsE.regs_out1 56 KS_tsE_1 KS_tsE_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtsE.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth PtsE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsE.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PtsE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. 
    change (SR.ps_pc PtsE.ps2) with 0x39520 in Hms. change (SR.ps_regs PtsE.ps2) with (map (fun i => (i, nth i PtsE.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtsE.ps2) with PtsE.cells2 in Hcells. unfold PtsE.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsE.regs0 PtsE.regs_out2 56 KS_tsE_2 KS_tsE_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtsE.regs_out2 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsE.regs_out2 E' R' 2 Hregs) by (clear; lia). cbn [nth PtsE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsE.regs_out2 E' R' 8 Hregs) by (clear; lia). cbn [nth PtsE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsE.regs_out2 E' R' 9 Hregs) by (clear; lia). cbn [nth PtsE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsE.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsE.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth PtsE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsE.regs_out2 E' R' 19 Hregs) by (clear; lia). cbn [nth PtsE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsE.regs_out2 E' R' 20 Hregs) by (clear; lia). cbn [nth PtsE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsE.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth PtsE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsE.regs_out2 E' R' 22 Hregs) by (clear; lia). cbn [nth PtsE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsE.regs_out2 E' R' 23 Hregs) by (clear; lia). cbn [nth PtsE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsF := LibSegBs_tsF_u.
Definition KS_tsF_0 : list nat := Eval vm_compute in (BG.kept_list 56 PtsF.regs0 PtsF.regs_out0).
Lemma KS_tsF_0_ok : BG.kept_ok 56 PtsF.regs0 PtsF.regs_out0 KS_tsF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsF_1 : list nat := Eval vm_compute in (BG.kept_list 56 PtsF.regs0 PtsF.regs_out1).
Lemma KS_tsF_1_ok : BG.kept_ok 56 PtsF.regs0 PtsF.regs_out1 KS_tsF_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tsF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 42%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 34%nat) + 1) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> 0 <= (V 42%nat) <= 16384 ->
  1 <= (V 36%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 54%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x394ec M) (st fx' R' 0x393d8 M')
        /\ (forall x, In x KS_tsF_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) - (V 42%nat))
        /\ 1 <= (((((V 36%nat) + ((18446744073709551615 * (V 42%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x394ec M) (st fx' R' 0x39520 M')
        /\ (forall x, In x KS_tsF_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 35%nat) + (((-1) * (V 36%nat)) + (V 42%nat)))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 54%nat)
        /\ (((((V 36%nat) + ((18446744073709551615 * (V 42%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G18 G20 G21 G22 pvzI16 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 pvzI17 pvzI18 K13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV49l; move HV49l before pvzI12; pose proof (proj2 pvzI12) as HV49r; move HV49r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV50l; move HV50l before pvzI13; pose proof (proj2 pvzI13) as HV50r; move HV50r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV51l; move HV51l before pvzI14; pose proof (proj2 pvzI14) as HV51r; move HV51r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV54l; move HV54l before pvzI15; pose proof (proj2 pvzI15) as HV54r; move HV54r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K11l; move K11l before pvzI17; pose proof (proj2 pvzI17) as K11r; move K11r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K12l; move K12l before pvzI18; pose proof (proj2 pvzI18) as K12r; move K12r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_54 := V 54%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 42%nat => Z_to_bv 64 vz_42 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 54%nat => Z_to_bv 64 vz_54 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 42%nat => vz_42 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 54%nat => vz_54 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PtsF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtsF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtsF.kn0).
  { unfold know_ok, PtsF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K13]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtsF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtsF.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtsF.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PtsF.ps0) with 0x393d8 in Hms. change (SR.ps_regs PtsF.ps0) with (map (fun i => (i, nth i PtsF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtsF.ps0) with PtsF.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsF.regs0 PtsF.regs_out0 56 KS_tsF_0 KS_tsF_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtsF.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PtsF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PtsF.ps1) with 0x39520 in Hms. change (SR.ps_regs PtsF.ps1) with (map (fun i => (i, nth i PtsF.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtsF.ps1) with PtsF.cells1 in Hcells. unfold PtsF.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsF.regs0 PtsF.regs_out1 56 KS_tsF_1 KS_tsF_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtsF.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsF.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PtsF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsF.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PtsF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsF.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PtsF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsF.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsF.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PtsF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsF.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PtsF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsF.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth PtsF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsF.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PtsF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsF.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth PtsF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsF.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PtsF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsDS := LibSegBs_tsDS_u.
Definition KS_tsDS : list nat := Eval vm_compute in (BG.kept_list 56 PtsDS.regs0 PtsDS.regs_out0).
Lemma KS_tsDS_ok : BG.kept_ok 56 PtsDS.regs0 PtsDS.regs_out0 KS_tsDS = true. Proof. vm_compute. reflexivity. Qed.
Lemma tsDS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 16384 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 34%nat) + 1) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 80)) -> L5.u8_at RSEGS M (V 34%nat) (V 39%nat) -> 0 <= (V 39%nat) <= 44 ->
  Z.testbit (V 39%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39470 M) (st fx' R' 0x59000 M')
        /\ (forall x, In x KS_tsDS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234648
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 39%nat) / 2) + 16384)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 39%nat) / 2)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G21 G22 pvzI7 K1 K2 pvzI8 K4 K5 K6 pvzI9 K8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PtsDS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtsDS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtsDS.kn0).
  { unfold know_ok, PtsDS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | byte_tac ltac:(clear - HV39l HV39r K7l K7r K8) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_false vz_39 ltac:(clear - HV39l HV39r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtsDS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtsDS.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtsDS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtsDS.ps0) with 0x59000 in Hms. change (SR.ps_regs PtsDS.ps0) with (map (fun i => (i, nth i PtsDS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtsDS.ps0) with PtsDS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsDS.regs0 PtsDS.regs_out0 56 KS_tsDS KS_tsDS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtsDS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsDS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsDS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtsDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsDS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtsDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtsDS.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PtsDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsDL := LibSegBs_tsDL_u.
Definition KS_tsDL : list nat := Eval vm_compute in (BG.kept_list 56 PtsDL.regs0 PtsDL.regs_out0).
Lemma KS_tsDL_ok : BG.kept_ok 56 PtsDL.regs0 PtsDL.regs_out0 KS_tsDL = true. Proof. vm_compute. reflexivity. Qed.
Lemma tsDL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 16384 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 34%nat) + 1) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 80)) -> L5.u8_at RSEGS M (V 34%nat) (V 39%nat) -> 0 <= (V 39%nat) <= 255 ->
  Z.testbit (V 39%nat) 0 = true -> L5.u64_at RSEGS M ((V 34%nat) + 8) (V 40%nat) -> 0 <= (V 40%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39470 M) (st fx' R' 0x59000 M')
        /\ (forall x, In x KS_tsDL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234648
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 16384)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G18 G19 G21 G22 pvzI8 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K10l; move K10l before pvzI11; pose proof (proj2 pvzI11) as K10r; move K10r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 39%nat => vz_39 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PtsDL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtsDL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtsDL.kn0).
  { unfold know_ok, PtsDL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | byte_tac ltac:(clear - HV39l HV39r K7l K7r K8) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_true vz_39 ltac:(clear - HV39l HV39r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV40l HV40r K10l K10r) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtsDL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtsDL.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtsDL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtsDL.ps0) with 0x59000 in Hms. change (SR.ps_regs PtsDL.ps0) with (map (fun i => (i, nth i PtsDL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtsDL.ps0) with PtsDL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsDL.regs0 PtsDL.regs_out0 56 KS_tsDL KS_tsDL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtsDL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsDL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsDL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsDL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsDL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtsDL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsDL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtsDL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtsDL.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PtsDL.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsD2 := LibSegBs_tsD2_u.
Definition KS_tsD2 : list nat := Eval vm_compute in (BG.kept_list 56 PtsD2.regs0 PtsD2.regs_out0).
Lemma KS_tsD2_ok : BG.kept_ok 56 PtsD2.regs0 PtsD2.regs_out0 KS_tsD2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tsD2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 16384 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 34%nat) + 1) -> getr R (reg 23) = Z_to_bv 64 (V 43%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 140735332483072 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 80)) -> L5.u8_at RSEGS M (V 34%nat) (V 39%nat) -> 0 <= (V 39%nat) <= 255 ->
  Z.testbit (V 39%nat) 0 = true -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355328 -> 0 <= (V 43%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39498 M) (st fx' R' 0x382d4 M')
        /\ (forall x, In x KS_tsD2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234696
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 41%nat) + (V 43%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 16384).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G18 G19 G21 G22 G23 pvzI9 K1 K2 pvzI10 K4 K5 K6 pvzI11 K8 K9 pvzI12 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K0l; move K0l before pvzI9; pose proof (proj2 pvzI9) as K0r; move K0r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K7l; move K7l before pvzI11; pose proof (proj2 pvzI11) as K7r; move K7r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K10l; move K10l before pvzI12; pose proof (proj2 pvzI12) as K10r; move K10r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K11l; move K11l before pvzI13; pose proof (proj2 pvzI13) as K11r; move K11r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 39%nat => vz_39 | 41%nat => vz_41 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PtsD2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtsD2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtsD2.kn0).
  { unfold know_ok, PtsD2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | byte_tac ltac:(clear - HV39l HV39r K7l K7r K8) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_true vz_39 ltac:(clear - HV39l HV39r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtsD2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtsD2.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtsD2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtsD2.ps0) with 0x382d4 in Hms. change (SR.ps_regs PtsD2.ps0) with (map (fun i => (i, nth i PtsD2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtsD2.ps0) with PtsD2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsD2.regs0 PtsD2.regs_out0 56 KS_tsD2 KS_tsD2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtsD2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsD2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtsD2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtsD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtsD2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtsD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtsD3 := LibSegBs_tsD3_u.
Definition KS_tsD3_0 : list nat := Eval vm_compute in (BG.kept_list 56 PtsD3.regs0 PtsD3.regs_out0).
Lemma KS_tsD3_0_ok : BG.kept_ok 56 PtsD3.regs0 PtsD3.regs_out0 KS_tsD3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsD3_1 : list nat := Eval vm_compute in (BG.kept_list 56 PtsD3.regs0 PtsD3.regs_out1).
Lemma KS_tsD3_1_ok : BG.kept_ok 56 PtsD3.regs0 PtsD3.regs_out1 KS_tsD3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tsD3_2 : list nat := Eval vm_compute in (BG.kept_list 56 PtsD3.regs0 PtsD3.regs_out2).
Lemma KS_tsD3_2_ok : BG.kept_ok 56 PtsD3.regs0 PtsD3.regs_out2 KS_tsD3_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tsD3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 53%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 16384 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 34%nat) + 1) -> getr R (reg 23) = Z_to_bv 64 (V 43%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> 140735332483072 <= (V 33%nat) <= 140737488355032 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 80) + 80 <= (V 33%nat) \/ (V 33%nat) + 296 <= ((V 2%nat) - 80)) -> L5.defined M ((V 33%nat) + 256) 8 -> L5.writable RSEGS M ((V 33%nat) + 256) 8 ->
  0 <= (V 53%nat) <= 16384 -> 0 <= (V 43%nat) <= 134217728 -> 1 <= (V 36%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 54%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 256) <= bv_unsigned a < ((V 33%nat) + 256) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 256) <= i < ((V 33%nat) + 256) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x394c8 M) (st fx' R' 0x59000 M')
        /\ (forall x, In x KS_tsD3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234732
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 43%nat) + (V 53%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ 1 <= (((V 53%nat) - 16384) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x394c8 M) (st fx' R' 0x393d8 M')
        /\ (forall x, In x KS_tsD3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) - (V 53%nat))
        /\ 1 <= (((((V 36%nat) + ((18446744073709551615 * (V 53%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64)
        /\ (((V 53%nat) - 16384) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x394c8 M) (st fx' R' 0x39520 M')
        /\ (forall x, In x KS_tsD3_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 35%nat) + (((-1) * (V 36%nat)) + (V 53%nat)))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 54%nat)
        /\ (((((V 36%nat) + ((18446744073709551615 * (V 53%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ (((V 53%nat) - 16384) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G8 G9 G10 G18 G19 G21 G22 G23 pvzI17 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 pvzI18 K12 K13 K14 K15 pvzI19 pvzI20 pvzI21 K19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV49l; move HV49l before pvzI12; pose proof (proj2 pvzI12) as HV49r; move HV49r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV50l; move HV50l before pvzI13; pose proof (proj2 pvzI13) as HV50r; move HV50r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV51l; move HV51l before pvzI14; pose proof (proj2 pvzI14) as HV51r; move HV51r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV53l; move HV53l before pvzI15; pose proof (proj2 pvzI15) as HV53r; move HV53r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV54l; move HV54l before pvzI16; pose proof (proj2 pvzI16) as HV54r; move HV54r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K0l; move K0l before pvzI17; pose proof (proj2 pvzI17) as K0r; move K0r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K11l; move K11l before pvzI18; pose proof (proj2 pvzI18) as K11r; move K11r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K16l; move K16l before pvzI19; pose proof (proj2 pvzI19) as K16r; move K16r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K17l; move K17l before pvzI20; pose proof (proj2 pvzI20) as K17r; move K17r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K18l; move K18l before pvzI21; pose proof (proj2 pvzI21) as K18r; move K18r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 53%nat => vz_53 | 54%nat => vz_54 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PtsD3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtsD3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtsD3.kn0).
  { unfold know_ok, PtsD3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K19]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtsD3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtsD3.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 256) <= bv_unsigned a < (vz_33 + 256) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtsD3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K11l K11r K13 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PtsD3.ps0) with 0x59000 in Hms. change (SR.ps_regs PtsD3.ps0) with (map (fun i => (i, nth i PtsD3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtsD3.ps0) with PtsD3.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsD3.regs0 PtsD3.regs_out0 56 KS_tsD3_0 KS_tsD3_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtsD3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsD3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsD3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsD3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsD3.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PtsD3.ps1) with 0x393d8 in Hms. change (SR.ps_regs PtsD3.ps1) with (map (fun i => (i, nth i PtsD3.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtsD3.ps1) with PtsD3.cells1 in Hcells. unfold PtsD3.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsD3.regs0 PtsD3.regs_out1 56 KS_tsD3_1 KS_tsD3_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtsD3.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsD3.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. 
    change (SR.ps_pc PtsD3.ps2) with 0x39520 in Hms. change (SR.ps_regs PtsD3.ps2) with (map (fun i => (i, nth i PtsD3.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtsD3.ps2) with PtsD3.cells2 in Hcells. unfold PtsD3.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtsD3.regs0 PtsD3.regs_out2 56 KS_tsD3_2 KS_tsD3_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtsD3.regs_out2 E' R' 1 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsD3.regs_out2 E' R' 2 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsD3.regs_out2 E' R' 8 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsD3.regs_out2 E' R' 9 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsD3.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsD3.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsD3.regs_out2 E' R' 19 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsD3.regs_out2 E' R' 20 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsD3.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsD3.regs_out2 E' R' 22 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtsD3.regs_out2 E' R' 23 Hregs) by (clear; lia). cbn [nth PtsD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

End PMSSRP.
