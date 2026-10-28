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
     BigLinkBase. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import BigLinkGlue_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import L5Kn_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_rpA_u LibSegBs_rpR0_u LibSegBs_rpB_u LibSegBs_rpF_u LibSegBs_rpG_u LibSegBs_rpSS_u LibSegBs_rpSL_u LibSegBs_rpES_u LibSegBs_rpEL_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMSRPP.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).

(* [comment removed for export] *)
Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5K.zpoly Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
  intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5K.zpoly_sound E Vz e z A Pz)).
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
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5K.zpoly_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5K.zpoly]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5K.zpoly_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5K.zpoly]; pvz_unfold ZA; reflexivity | solve_modk k ].
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
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5K.zpoly]; pvz_unfold ZA; f_equal; clear; lia]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5K.zpoly]; pvz_unfold ZA; f_equal; clear; lia ].
(* [comment removed for export] *)
Module PrpA := LibSegBs_rpA_u.
Definition KS_rpA_0 : list nat := Eval vm_compute in (BG.kept_list 56 PrpA.regs0 PrpA.regs_out0).
Lemma KS_rpA_0_ok : BG.kept_ok 56 PrpA.regs0 PrpA.regs_out0 KS_rpA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rpA_1 : list nat := Eval vm_compute in (BG.kept_list 56 PrpA.regs0 PrpA.regs_out1).
Lemma KS_rpA_1_ok : BG.kept_ok 56 PrpA.regs0 PrpA.regs_out1 KS_rpA_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rpA_2 : list nat := Eval vm_compute in (BG.kept_list 56 PrpA.regs0 PrpA.regs_out2).
Lemma KS_rpA_2_ok : BG.kept_ok 56 PrpA.regs0 PrpA.regs_out2 KS_rpA_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rpA_3 : list nat := Eval vm_compute in (BG.kept_list 56 PrpA.regs0 PrpA.regs_out3).
Lemma KS_rpA_3_ok : BG.kept_ok 56 PrpA.regs0 PrpA.regs_out3 KS_rpA_3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma rpA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483072 <= (V 33%nat) <= 140737488355032 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 33%nat) \/ (V 33%nat) + 296 <= ((V 2%nat) - 32)) -> L5.u64_at RSEGS M ((V 33%nat) + 288) (V 36%nat) -> 0 <= (V 36%nat) <= 16384 ->
  0 <= (V 35%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 32) <= bv_unsigned a < ((V 2%nat) - 32) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 32) <= i < ((V 2%nat) - 32) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x39290 M) (st fx' R' 0x39384 M')
        /\ (forall x, In x KS_rpA_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ (((V 35%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x39290 M) (st fx' R' 0x392c0 M')
        /\ (forall x, In x KS_rpA_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ (V 35%nat) <= (V 36%nat)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ 1 <= (((V 35%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x39290 M) (st fx' R' 0x39318 M')
        /\ (forall x, In x KS_rpA_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ (V 36%nat) < (V 35%nat)
        /\ 1 <= (((V 36%nat) - 0) mod 2 ^ 64)
        /\ 1 <= (((V 35%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x39290 M) (st fx' R' 0x392f0 M')
        /\ (forall x, In x KS_rpA_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ (((V 36%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 35%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 G12 pvzI6 K1 K2 pvzI7 K4 K5 K6 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K8l; move K8l before pvzI9; pose proof (proj2 pvzI9) as K8r; move K8r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PrpA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrpA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrpA.kn0).
  { unfold know_ok, PrpA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrpA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrpA.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 32) <= bv_unsigned a < (vz_2 - 32) + 32) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PrpA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PrpA.ps0) with 0x39384 in Hms. change (SR.ps_regs PrpA.ps0) with (map (fun i => (i, nth i PrpA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PrpA.ps0) with PrpA.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PrpA.regs0 PrpA.regs_out0 56 KS_rpA_0 KS_rpA_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PrpA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrpA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrpA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PrpA.ps1) with 0x392c0 in Hms. change (SR.ps_regs PrpA.ps1) with (map (fun i => (i, nth i PrpA.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PrpA.ps1) with PrpA.cells1 in Hcells. unfold PrpA.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PrpA.regs0 PrpA.regs_out1 56 KS_rpA_1 KS_rpA_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PrpA.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PrpA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpA.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PrpA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpA.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PrpA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpA.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PrpA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpA.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PrpA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc PrpA.ps2) with 0x39318 in Hms. change (SR.ps_regs PrpA.ps2) with (map (fun i => (i, nth i PrpA.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PrpA.ps2) with PrpA.cells2 in Hcells. unfold PrpA.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PrpA.regs0 PrpA.regs_out2 56 KS_rpA_2 KS_rpA_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PrpA.regs_out2 E' R' 2 Hregs) by (clear; lia). cbn [nth PrpA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpA.regs_out2 E' R' 8 Hregs) by (clear; lia). cbn [nth PrpA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpA.regs_out2 E' R' 9 Hregs) by (clear; lia). cbn [nth PrpA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpA.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PrpA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpA.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth PrpA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. 
    change (SR.ps_pc PrpA.ps3) with 0x392f0 in Hms. change (SR.ps_regs PrpA.ps3) with (map (fun i => (i, nth i PrpA.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PrpA.ps3) with PrpA.cells3 in Hcells. unfold PrpA.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PrpA.regs0 PrpA.regs_out3 56 KS_rpA_3 KS_rpA_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PrpA.regs_out3 E' R' 2 Hregs) by (clear; lia). cbn [nth PrpA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpA.regs_out3 E' R' 8 Hregs) by (clear; lia). cbn [nth PrpA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpA.regs_out3 E' R' 9 Hregs) by (clear; lia). cbn [nth PrpA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpA.regs_out3 E' R' 11 Hregs) by (clear; lia). cbn [nth PrpA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpA.regs_out3 E' R' 18 Hregs) by (clear; lia). cbn [nth PrpA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrpR0 := LibSegBs_rpR0_u.
Definition KS_rpR0_0 : list nat := Eval vm_compute in (BG.kept_list 56 PrpR0.regs0 PrpR0.regs_out0).
Lemma KS_rpR0_0_ok : BG.kept_ok 56 PrpR0.regs0 PrpR0.regs_out0 KS_rpR0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rpR0_1 : list nat := Eval vm_compute in (BG.kept_list 56 PrpR0.regs0 PrpR0.regs_out1).
Lemma KS_rpR0_1_ok : BG.kept_ok 56 PrpR0.regs0 PrpR0.regs_out1 KS_rpR0_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma rpR0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483072 <= (V 33%nat) <= 140737488355032 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 33%nat) \/ (V 33%nat) + 296 <= ((V 2%nat) - 32)) -> L5.u64_at RSEGS M ((V 33%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 33%nat) + 264) (V 42%nat) ->
  1 <= (V 35%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x392f0 M) (st fx' R' 0x39318 M')
        /\ (forall x, In x KS_rpR0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 16384
        /\ 16384 < (V 35%nat))
      \/ (msteps RSEGS (st fx R 0x392f0 M) (st fx' R' 0x382d4 M')
        /\ (forall x, In x KS_rpR0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234244
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 16384
        /\ (V 35%nat) <= 16384)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K8l; move K8l before pvzI8; pose proof (proj2 pvzI8) as K8r; move K8r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PrpR0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrpR0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrpR0.kn0).
  { unfold know_ok, PrpR0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrpR0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrpR0.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PrpR0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PrpR0.ps0) with 0x39318 in Hms. change (SR.ps_regs PrpR0.ps0) with (map (fun i => (i, nth i PrpR0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PrpR0.ps0) with PrpR0.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PrpR0.regs0 PrpR0.regs_out0 56 KS_rpR0_0 KS_rpR0_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PrpR0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PrpR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PrpR0.ps1) with 0x382d4 in Hms. change (SR.ps_regs PrpR0.ps1) with (map (fun i => (i, nth i PrpR0.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PrpR0.ps1) with PrpR0.cells1 in Hcells. unfold PrpR0.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PrpR0.regs0 PrpR0.regs_out1 56 KS_rpR0_1 KS_rpR0_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PrpR0.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PrpR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpR0.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PrpR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpR0.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PrpR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpR0.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PrpR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrpB := LibSegBs_rpB_u.
Definition KS_rpB_0 : list nat := Eval vm_compute in (BG.kept_list 56 PrpB.regs0 PrpB.regs_out0).
Lemma KS_rpB_0_ok : BG.kept_ok 56 PrpB.regs0 PrpB.regs_out0 KS_rpB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_rpB_1 : list nat := Eval vm_compute in (BG.kept_list 56 PrpB.regs0 PrpB.regs_out1).
Lemma KS_rpB_1_ok : BG.kept_ok 56 PrpB.regs0 PrpB.regs_out1 KS_rpB_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma rpB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 10) = Z_to_bv 64 (V 43%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483072 <= (V 33%nat) <= 140737488355032 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 33%nat) \/ (V 33%nat) + 296 <= ((V 2%nat) - 32)) -> L5.u64_at RSEGS M ((V 33%nat) + 264) (V 42%nat) -> L5.writable RSEGS M ((V 33%nat) + 280) 16 ->
  0 <= (V 43%nat) <= 16384 -> 1 <= (V 35%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 280) <= bv_unsigned a < ((V 33%nat) + 280) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 280) <= i < ((V 33%nat) + 280) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x39304 M) (st fx' R' 0x39318 M')
        /\ (forall x, In x KS_rpB_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 43%nat)
        /\ (V 43%nat) < (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 288) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 280) (V 42%nat))
      \/ (msteps RSEGS (st fx R 0x39304 M) (st fx' R' 0x392c0 M')
        /\ (forall x, In x KS_rpB_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 43%nat)
        /\ (V 35%nat) <= (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 288) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 280) (V 42%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 pvzI9 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K8l; move K8l before pvzI9; pose proof (proj2 pvzI9) as K8r; move K8r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K9l; move K9l before pvzI10; pose proof (proj2 pvzI10) as K9r; move K9r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 42%nat => vz_42 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PrpB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrpB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrpB.kn0).
  { unfold know_ok, PrpB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrpB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrpB.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 280) <= bv_unsigned a < (vz_33 + 280) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PrpB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PrpB.ps0) with 0x39318 in Hms. change (SR.ps_regs PrpB.ps0) with (map (fun i => (i, nth i PrpB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PrpB.ps0) with PrpB.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PrpB.regs0 PrpB.regs_out0 56 KS_rpB_0 KS_rpB_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PrpB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrpB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrpB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K8l K8r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. 
  - right.
    change (SR.ps_pc PrpB.ps1) with 0x392c0 in Hms. change (SR.ps_regs PrpB.ps1) with (map (fun i => (i, nth i PrpB.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PrpB.ps1) with PrpB.cells1 in Hcells. unfold PrpB.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PrpB.regs0 PrpB.regs_out1 56 KS_rpB_1 KS_rpB_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PrpB.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PrpB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PrpB.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PrpB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K8l K8r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrpF := LibSegBs_rpF_u.
Definition KS_rpF : list nat := Eval vm_compute in (BG.kept_list 56 PrpF.regs0 PrpF.regs_out0).
Lemma KS_rpF_ok : BG.kept_ok 56 PrpF.regs0 PrpF.regs_out0 KS_rpF = true. Proof. vm_compute. reflexivity. Qed.
Lemma rpF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483072 <= (V 33%nat) <= 140737488355032 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 33%nat) \/ (V 33%nat) + 296 <= ((V 2%nat) - 32)) -> L5.u64_at RSEGS M ((V 33%nat) + 280) (V 37%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 256) (V 38%nat) ->
  1 <= (V 35%nat) <= 16384 -> 1 <= (V 36%nat) <= 16384 -> 1 <= (V 37%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x392c0 M) (st fx' R' 0x392d8 M')
        /\ (forall x, In x KS_rpF -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 35%nat) + (V 37%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G11 G18 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 pvzI11 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K9l; move K9l before pvzI11; pose proof (proj2 pvzI11) as K9r; move K9r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K10l; move K10l before pvzI12; pose proof (proj2 pvzI12) as K10r; move K10r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PrpF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrpF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrpF.kn0).
  { unfold know_ok, PrpF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear - HV37l HV37r K10l K10r) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrpF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrpF.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PrpF.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrpF.ps0) with 0x392d8 in Hms. change (SR.ps_regs PrpF.ps0) with (map (fun i => (i, nth i PrpF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrpF.ps0) with PrpF.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrpF.regs0 PrpF.regs_out0 56 KS_rpF KS_rpF_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrpF.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpF.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PrpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PrpF.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PrpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrpG := LibSegBs_rpG_u.
Definition KS_rpG : list nat := Eval vm_compute in (BG.kept_list 56 PrpG.regs0 PrpG.regs_out0).
Lemma KS_rpG_ok : BG.kept_ok 56 PrpG.regs0 PrpG.regs_out0 KS_rpG = true. Proof. vm_compute. reflexivity. Qed.
Lemma rpG_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 11) = Z_to_bv 64 (V 48%nat) -> getr R (reg 12) = Z_to_bv 64 (V 49%nat) -> getr R (reg 13) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> 140735332483072 <= (V 33%nat) <= 140737488355032 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 33%nat) \/ (V 33%nat) + 296 <= ((V 2%nat) - 32)) -> L5.writable RSEGS M ((V 33%nat) + 256) 8 -> L5.writable RSEGS M ((V 33%nat) + 280) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 256) <= bv_unsigned a < ((V 33%nat) + 256) + 8) -> ~ (((V 33%nat) + 280) <= bv_unsigned a < ((V 33%nat) + 280) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 256) <= i < ((V 33%nat) + 256) + 8) -> ~ (((V 33%nat) + 280) <= i < ((V 33%nat) + 280) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x392d8 M) (st fx' R' 0x39384 M')
        /\ (forall x, In x KS_rpG -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 35%nat)
        /\ bv_unsigned (getr R' (reg 13)) = (((V 35%nat) + (V 50%nat)) mod 2 ^ 64)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 288) ((((18446744073709551615 * (V 35%nat)) mod 2 ^ 64) + (V 48%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 280) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 256) (((V 35%nat) + (V 50%nat)) mod 2 ^ 64)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G10 G11 G12 G13 G18 pvzI13 K1 K2 K3 K4 K5 K6 pvzI14 K8 K9 K10 K11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV45l; move HV45l before pvzI7; pose proof (proj2 pvzI7) as HV45r; move HV45r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV47l; move HV47l before pvzI9; pose proof (proj2 pvzI9) as HV47r; move HV47r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV48l; move HV48l before pvzI10; pose proof (proj2 pvzI10) as HV48r; move HV48r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV49l; move HV49l before pvzI11; pose proof (proj2 pvzI11) as HV49r; move HV49r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV50l; move HV50l before pvzI12; pose proof (proj2 pvzI12) as HV50r; move HV50r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K0l; move K0l before pvzI13; pose proof (proj2 pvzI13) as K0r; move K0r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K7l; move K7l before pvzI14; pose proof (proj2 pvzI14) as K7r; move K7r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 37%nat => Z_to_bv 64 vz_37 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 37%nat => vz_37 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PrpG.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrpG.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrpG.kn0).
  { unfold know_ok, PrpG.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9; lia | clear - HV33l HV33r K7l K7r K9; lia | clear - HV33l HV33r K7l K7r K9; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9; lia | clear - HV33l HV33r K7l K7r K9; lia | clear - HV33l HV33r K7l K7r K9; lia | exactA K11]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrpG.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrpG.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 256) <= bv_unsigned a < (vz_33 + 256) + 8) -> ~ ((vz_33 + 280) <= bv_unsigned a < (vz_33 + 280) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PrpG.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrpG.ps0) with 0x39384 in Hms. change (SR.ps_regs PrpG.ps0) with (map (fun i => (i, nth i PrpG.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrpG.ps0) with PrpG.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrpG.regs0 PrpG.regs_out0 56 KS_rpG KS_rpG_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrpG.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PrpG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpG.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PrpG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpG.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PrpG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpG.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PrpG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpG.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrpG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpG.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PrpG.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PrpG.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PrpG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrpSS := LibSegBs_rpSS_u.
Definition KS_rpSS : list nat := Eval vm_compute in (BG.kept_list 56 PrpSS.regs0 PrpSS.regs_out0).
Lemma KS_rpSS_ok : BG.kept_ok 56 PrpSS.regs0 PrpSS.regs_out0 KS_rpSS = true. Proof. vm_compute. reflexivity. Qed.
Lemma rpSS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483072 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 32)) -> L5.u8_at RSEGS M (V 34%nat) (V 39%nat) -> 0 <= (V 39%nat) <= 44 ->
  Z.testbit (V 39%nat) 0 = false -> L5.writable RSEGS M (V 34%nat) 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 34%nat) + 0) <= bv_unsigned a < ((V 34%nat) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 34%nat) + 0) <= i < ((V 34%nat) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39318 M) (st fx' R' 0x39398 M')
        /\ (forall x, In x KS_rpSS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234316
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 35%nat)
        /\ (L5.u8_at RSEGS M' (V 34%nat) 0 /\ L5.u8_at RSEGS M' ((V 34%nat) + 1) 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 pvzI6 K1 K2 pvzI7 K4 K5 K6 pvzI8 K8 K9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PrpSS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrpSS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrpSS.kn0).
  { unfold know_ok, PrpSS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | byte_tac ltac:(clear - HV39l HV39r K7l K7r K8) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_false vz_39 ltac:(clear - HV39l HV39r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | exactA K9]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrpSS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrpSS.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_34 + 0) <= bv_unsigned a < (vz_34 + 0) + 2) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PrpSS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K3l K3r K5 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrpSS.ps0) with 0x39398 in Hms. change (SR.ps_regs PrpSS.ps0) with (map (fun i => (i, nth i PrpSS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrpSS.ps0) with PrpSS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrpSS.regs0 PrpSS.regs_out0 56 KS_rpSS KS_rpSS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrpSS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PrpSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpSS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrpSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpSS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrpSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpSS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PrpSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8x2_of_KWord2a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrpSL := LibSegBs_rpSL_u.
Definition KS_rpSL : list nat := Eval vm_compute in (BG.kept_list 56 PrpSL.regs0 PrpSL.regs_out0).
Lemma KS_rpSL_ok : BG.kept_ok 56 PrpSL.regs0 PrpSL.regs_out0 KS_rpSL = true. Proof. vm_compute. reflexivity. Qed.
Lemma rpSL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> 140735332483072 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 32)) -> L5.u8_at RSEGS M (V 34%nat) (V 39%nat) -> 0 <= (V 39%nat) <= 255 ->
  Z.testbit (V 39%nat) 0 = true -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355328 -> L5.writable RSEGS M (V 41%nat) 1 ->
  L5.writable RSEGS M ((V 34%nat) + 8) 8 -> (((V 2%nat) - 32) + 32 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 32)) -> ((V 34%nat) + 24 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 34%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> ~ (((V 34%nat) + 8) <= bv_unsigned a < ((V 34%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 1) -> ~ (((V 34%nat) + 8) <= i < ((V 34%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39318 M) (st fx' R' 0x39398 M')
        /\ (forall x, In x KS_rpSL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234316
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 34%nat) + 8) 0
        /\ L5.u8_at RSEGS M' (V 41%nat) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 pvzI7 K1 K2 pvzI8 K4 K5 K6 pvzI9 K8 K9 pvzI10 K11 K12 K13 K14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K10l; move K10l before pvzI10; pose proof (proj2 pvzI10) as K10r; move K10r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 39%nat => vz_39 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PrpSL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrpSL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrpSL.kn0).
  { unfold know_ok, PrpSL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K13) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K13) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K13; lia | clear - HV2l HV2r K0l K0r K5 K13; lia | clear - HV2l HV2r K0l K0r K5 K13; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5 K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5 K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5 K14) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5 K14) | evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear - HV34l HV34r K3l K3r K5 K14; lia | clear - HV34l HV34r K3l K3r K5 K14; lia | byte_tac ltac:(clear - HV39l HV39r K7l K7r K8) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_true vz_39 ltac:(clear - HV39l HV39r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5 K14) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K13 K14) | clear - HV34l HV34r K3l K3r K5 K14; lia | clear - HV34l HV34r K3l K3r K5 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K13 K14) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K13 K14) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K10l K10r K13 K14; lia | clear - HV41l HV41r K10l K10r K13 K14; lia | clear - HV41l HV41r K10l K10r K13 K14; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5 K14) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K3l K3r K5 K14; lia | clear - HV34l HV34r K3l K3r K5 K14; lia | clear - HV34l HV34r K3l K3r K5 K14; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K13 K14) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrpSL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrpSL.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_41 + 0) <= bv_unsigned a < (vz_41 + 0) + 1) -> ~ ((vz_34 + 8) <= bv_unsigned a < (vz_34 + 8) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PrpSL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV41l HV41r K10l K10r K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV41l HV41r K10l K10r K13 K14 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K3l K3r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K3l K3r K5 K14 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrpSL.ps0) with 0x39398 in Hms. change (SR.ps_regs PrpSL.ps0) with (map (fun i => (i, nth i PrpSL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrpSL.ps0) with PrpSL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrpSL.regs0 PrpSL.regs_out0 56 KS_rpSL KS_rpSL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrpSL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PrpSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpSL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrpSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpSL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrpSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpSL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PrpSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K3l K3r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV41l HV41r K10l K10r K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrpES := LibSegBs_rpES_u.
Definition KS_rpES : list nat := Eval vm_compute in (BG.kept_list 56 PrpES.regs0 PrpES.regs_out0).
Lemma KS_rpES_ok : BG.kept_ok 56 PrpES.regs0 PrpES.regs_out0 KS_rpES = true. Proof. vm_compute. reflexivity. Qed.
Lemma rpES_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> 140735332483072 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 32)) -> L5.u8_at RSEGS M (V 34%nat) (V 39%nat) -> 0 <= (V 39%nat) <= 44 ->
  Z.testbit (V 39%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3934c M) (st fx' R' 0x39384 M')
        /\ (forall x, In x KS_rpES -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 34%nat) + 1)
        /\ bv_unsigned (getr R' (reg 11)) = ((V 39%nat) / 2)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G18 pvzI10 K1 K2 K3 K4 K5 K6 pvzI11 K8 K9 K10 pvzI12 K12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV45l; move HV45l before pvzI7; pose proof (proj2 pvzI7) as HV45r; move HV45r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV47l; move HV47l before pvzI9; pose proof (proj2 pvzI9) as HV47r; move HV47r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K0l; move K0l before pvzI10; pose proof (proj2 pvzI10) as K0r; move K0r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K7l; move K7l before pvzI11; pose proof (proj2 pvzI11) as K7r; move K7r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K11l; move K11l before pvzI12; pose proof (proj2 pvzI12) as K11r; move K11r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 39%nat => Z_to_bv 64 vz_39 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 39%nat => vz_39 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PrpES.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrpES.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrpES.kn0).
  { unfold know_ok, PrpES.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9) | evalEk ZA ltac:(clear - HV39l HV39r K11l K11r K12) | clear - HV34l HV34r K7l K7r K9; lia | clear - HV34l HV34r K7l K7r K9; lia | byte_tac ltac:(clear - HV39l HV39r K11l K11r K12) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K11l K11r K12) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K11l K11r K12) | clear; lia | rewrite (L5K.land1_bit0_false vz_39 ltac:(clear - HV39l HV39r K11l K11r K12; lia) K12); clear; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrpES.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrpES.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PrpES.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrpES.ps0) with 0x39384 in Hms. change (SR.ps_regs PrpES.ps0) with (map (fun i => (i, nth i PrpES.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrpES.ps0) with PrpES.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrpES.regs0 PrpES.regs_out0 56 KS_rpES KS_rpES_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrpES.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PrpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpES.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PrpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpES.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PrpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpES.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PrpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpES.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpES.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrpES.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  rewrite (BG.out_reg PrpES.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PrpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PrpEL := LibSegBs_rpEL_u.
Definition KS_rpEL : list nat := Eval vm_compute in (BG.kept_list 56 PrpEL.regs0 PrpEL.regs_out0).
Lemma KS_rpEL_ok : BG.kept_ok 56 PrpEL.regs0 PrpEL.regs_out0 KS_rpEL = true. Proof. vm_compute. reflexivity. Qed.
Lemma rpEL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483104 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 32) 32 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> 140735332483072 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 32) + 32 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 32)) -> L5.u8_at RSEGS M (V 34%nat) (V 39%nat) -> 0 <= (V 39%nat) <= 255 ->
  Z.testbit (V 39%nat) 0 = true -> L5.u64_at RSEGS M ((V 34%nat) + 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 41%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3934c M) (st fx' R' 0x39384 M')
        /\ (forall x, In x KS_rpEL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G18 pvzI12 K1 K2 K3 K4 K5 K6 pvzI13 K8 K9 K10 pvzI14 K12 K13 K14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV44l; move HV44l before pvzI8; pose proof (proj2 pvzI8) as HV44r; move HV44r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV45l; move HV45l before pvzI9; pose proof (proj2 pvzI9) as HV45r; move HV45r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV46l; move HV46l before pvzI10; pose proof (proj2 pvzI10) as HV46r; move HV46r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV47l; move HV47l before pvzI11; pose proof (proj2 pvzI11) as HV47r; move HV47r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K0l; move K0l before pvzI12; pose proof (proj2 pvzI12) as K0r; move K0r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K7l; move K7l before pvzI13; pose proof (proj2 pvzI13) as K7r; move K7r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K11l; move K11l before pvzI14; pose proof (proj2 pvzI14) as K11r; move K11r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 48%nat. }
  assert (HR: regs_ok E PrpEL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PrpEL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PrpEL.kn0).
  { unfold know_ok, PrpEL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K9; lia | clear - HV2l HV2r K0l K0r K9; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9) | evalEk ZA ltac:(clear - HV39l HV39r K11l K11r K12) | clear - HV34l HV34r K7l K7r K9; lia | clear - HV34l HV34r K7l K7r K9; lia | byte_tac ltac:(clear - HV39l HV39r K11l K11r K12) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K11l K11r K12) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K11l K11r K12) | clear; lia | rewrite (L5K.land1_bit0_true vz_39 ltac:(clear - HV39l HV39r K11l K11r K12; lia) K12); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV34l HV34r K7l K7r K9; lia | clear - HV34l HV34r K7l K7r K9; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV34l HV34r K7l K7r K9; lia | clear - HV34l HV34r K7l K7r K9; lia | exactA K14]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PrpEL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PrpEL.NX0 with 56%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PrpEL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PrpEL.ps0) with 0x39384 in Hms. change (SR.ps_regs PrpEL.ps0) with (map (fun i => (i, nth i PrpEL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PrpEL.ps0) with PrpEL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PrpEL.regs0 PrpEL.regs_out0 56 KS_rpEL KS_rpEL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PrpEL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PrpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpEL.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PrpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpEL.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PrpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpEL.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PrpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpEL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PrpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PrpEL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PrpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PrpEL.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PrpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End PMSRPP.
