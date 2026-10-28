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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_bpaE0_u LibSegBs_bpaE2_u LibSegBs_bpaHX_u LibSegBs_bpaH0_u LibSegBs_bpaH1_u LibSegBs_bpaH2_u LibSegBs_bpaH3_u LibSegBs_bpaH4_u LibSegBs_bpaR2e_u LibSegBs_bpaR20_u LibSegBs_bpaR21_u LibSegBs_bpaN2_u LibSegBs_bpaR3e_u LibSegBs_bpaR30_u LibSegBs_bpaR31_u LibSegBs_bpaN3_u LibSegBs_bpaX0_u LibSegBs_bpaX1_u LibSegBs_bpaJ74_u LibSegBs_bpaJ2c_u LibSegBs_bpaJ68_u LibSegBs_bpaME_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSPAP.
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
Module PbpaE0 := LibSegBs_bpaE0_u.
Definition KS_bpaE0 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaE0.regs0 PbpaE0.regs_out0).
Lemma KS_bpaE0_ok : BG.kept_ok 64 PbpaE0.regs0 PbpaE0.regs_out0 KS_bpaE0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaE0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 140735332483184 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> 140735332483184 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  140735332483184 <= (V 36%nat) <= 140737488355056 -> aligned (V 36%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 36%nat) \/ (V 36%nat) + 272 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M ((V 33%nat) + 256) (V 36%nat) -> L5.u64_at RSEGS M (V 36%nat) 740792 -> L5.u32_at RSEGS M ((V 36%nat) + 152) 0 -> ((V 33%nat) + 416 <= (V 36%nat) \/ (V 36%nat) + 272 <= (V 33%nat)) ->
  ((V 36%nat) + 272 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 36%nat)) -> L5.u8_at RSEGS M ((V 33%nat) + 9) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 112) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 112) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36bc0 M) (st fx' R' 0x36c58 M')
        /\ (forall x, In x KS_bpaE0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 80964
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 20) = Z_to_bv 64 1
        /\ getr R' (reg 21) = Z_to_bv 64 40
        /\ getr R' (reg 22) = Z_to_bv 64 4
        /\ getr R' (reg 23) = Z_to_bv 64 2
        /\ getr R' (reg 24) = Z_to_bv 64 79632
        /\ getr R' (reg 25) = Z_to_bv 64 256
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 G12 pvzI6 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 pvzI9 K13 K14 K15 K16 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PbpaE0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaE0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaE0.kn0).
  { unfold know_ok, PbpaE0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K14; lia | clear - HV2l HV2r K0l K0r K5 K8 K14; lia | clear - HV2l HV2r K0l K0r K5 K8 K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K19) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K19) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K19) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K20) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K20) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K20) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K20) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11 K20; lia | clear - HV34l HV34r K6l K6r K8 K11 K20; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K20) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K19) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | clear - HV33l HV33r K3l K3r K5 K11 K19; lia | clear - HV33l HV33r K3l K3r K5 K11 K19; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K12l K12r K14 K19 K20; lia | clear - HV36l HV36r K12l K12r K14 K19 K20; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K12l K12r K14 K19 K20; lia | clear - HV36l HV36r K12l K12r K14 K19 K20; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K19) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K11 K19; lia | clear - HV33l HV33r K3l K3r K5 K11 K19; lia | byte_tac ltac:(clear) | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaE0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaE0.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 112) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbpaE0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaE0.ps0) with 0x36c58 in Hms. change (SR.ps_regs PbpaE0.ps0) with (map (fun i => (i, nth i PbpaE0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaE0.ps0) with PbpaE0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaE0.regs0 PbpaE0.regs_out0 64 KS_bpaE0 KS_bpaE0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaE0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpaE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpaE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpaE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpaE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpaE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpaE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpaE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpaE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpaE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbpaE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbpaE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbpaE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE0.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbpaE0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaE2 := LibSegBs_bpaE2_u.
Definition KS_bpaE2 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaE2.regs0 PbpaE2.regs_out0).
Lemma KS_bpaE2_ok : BG.kept_ok 64 PbpaE2.regs0 PbpaE2.regs_out0 KS_bpaE2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaE2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 140735332483184 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> 140735332483184 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  140735332483184 <= (V 36%nat) <= 140737488355056 -> aligned (V 36%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 36%nat) \/ (V 36%nat) + 272 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M ((V 33%nat) + 256) (V 36%nat) -> L5.u64_at RSEGS M (V 36%nat) 740792 -> L5.u32_at RSEGS M ((V 36%nat) + 152) 2 -> ((V 33%nat) + 416 <= (V 36%nat) \/ (V 36%nat) + 272 <= (V 33%nat)) ->
  ((V 36%nat) + 272 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 36%nat)) -> L5.u8_at RSEGS M ((V 33%nat) + 9) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 112) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 112) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36bc0 M) (st fx' R' 0x36c58 M')
        /\ (forall x, In x KS_bpaE2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 80964
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 20) = Z_to_bv 64 1
        /\ getr R' (reg 21) = Z_to_bv 64 40
        /\ getr R' (reg 22) = Z_to_bv 64 4
        /\ getr R' (reg 23) = Z_to_bv 64 2
        /\ getr R' (reg 24) = Z_to_bv 64 79632
        /\ getr R' (reg 25) = Z_to_bv 64 256
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 G12 pvzI6 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 pvzI9 K13 K14 K15 K16 K17 K18 K19 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PbpaE2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaE2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaE2.kn0).
  { unfold know_ok, PbpaE2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K14; lia | clear - HV2l HV2r K0l K0r K5 K8 K14; lia | clear - HV2l HV2r K0l K0r K5 K8 K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K19) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K19) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K19) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K20) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K20) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K20) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K20) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11 K20; lia | clear - HV34l HV34r K6l K6r K8 K11 K20; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K20) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K19) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | clear - HV33l HV33r K3l K3r K5 K11 K19; lia | clear - HV33l HV33r K3l K3r K5 K11 K19; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K12l K12r K14 K19 K20; lia | clear - HV36l HV36r K12l K12r K14 K19 K20; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K12l K12r K14 K19 K20; lia | clear - HV36l HV36r K12l K12r K14 K19 K20; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14 K19 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K19) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K11 K19; lia | clear - HV33l HV33r K3l K3r K5 K11 K19; lia | byte_tac ltac:(clear) | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaE2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaE2.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 112) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbpaE2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaE2.ps0) with 0x36c58 in Hms. change (SR.ps_regs PbpaE2.ps0) with (map (fun i => (i, nth i PbpaE2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaE2.ps0) with PbpaE2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaE2.regs0 PbpaE2.regs_out0 64 KS_bpaE2 KS_bpaE2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaE2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpaE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpaE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpaE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpaE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpaE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpaE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpaE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpaE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpaE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbpaE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbpaE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbpaE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaE2.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbpaE2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K8 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaHX := LibSegBs_bpaHX_u.
Definition KS_bpaHX : list nat := Eval vm_compute in (BG.kept_list 64 PbpaHX.regs0 PbpaHX.regs_out0).
Lemma KS_bpaHX_ok : BG.kept_ok 64 PbpaHX.regs0 PbpaHX.regs_out0 KS_bpaHX = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaHX_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 54%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 58%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 60%nat) -> 140735332483184 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> L5.u8_at RSEGS M ((V 33%nat) + 8) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36c58 M) (st fx' R' 0x36e54 M')
        /\ (forall x, In x KS_bpaHX -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 60%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI16 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 pvzI17 K15 K16 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV52l; move HV52l before pvzI7; pose proof (proj2 pvzI7) as HV52r; move HV52r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV53l; move HV53l before pvzI8; pose proof (proj2 pvzI8) as HV53r; move HV53r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV54l; move HV54l before pvzI9; pose proof (proj2 pvzI9) as HV54r; move HV54r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV55l; move HV55l before pvzI10; pose proof (proj2 pvzI10) as HV55r; move HV55r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV56l; move HV56l before pvzI11; pose proof (proj2 pvzI11) as HV56r; move HV56r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV57l; move HV57l before pvzI12; pose proof (proj2 pvzI12) as HV57r; move HV57r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV58l; move HV58l before pvzI13; pose proof (proj2 pvzI13) as HV58r; move HV58r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV59l; move HV59l before pvzI14; pose proof (proj2 pvzI14) as HV59r; move HV59r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV60l; move HV60l before pvzI15; pose proof (proj2 pvzI15) as HV60r; move HV60r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K14l; move K14l before pvzI17; pose proof (proj2 pvzI17) as K14r; move K14r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PbpaHX.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaHX.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaHX.kn0).
  { unfold know_ok, PbpaHX.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K14l K14r K16; lia | clear - HV33l HV33r K14l K14r K16; lia | byte_tac ltac:(clear) | exactA K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaHX.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaHX.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbpaHX.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaHX.ps0) with 0x36e54 in Hms. change (SR.ps_regs PbpaHX.ps0) with (map (fun i => (i, nth i PbpaHX.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaHX.ps0) with PbpaHX.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaHX.regs0 PbpaHX.regs_out0 64 KS_bpaHX KS_bpaHX_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaHX.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpaHX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaHX.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpaHX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaHX.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpaHX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaHX.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpaHX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaHX.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaHX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaHX.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpaHX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaHX.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpaHX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaHX.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpaHX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaHX.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpaHX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaHX.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbpaHX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaHX.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbpaHX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaHX.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbpaHX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbpaHX.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbpaHX.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaH0 := LibSegBs_bpaH0_u.
Definition KS_bpaH0 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaH0.regs0 PbpaH0.regs_out0).
Lemma KS_bpaH0_ok : BG.kept_ok 64 PbpaH0.regs0 PbpaH0.regs_out0 KS_bpaH0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaH0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 140735332483184 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> 140735332483184 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u8_at RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 45%nat) -> 4136 <= (V 45%nat) <= 140737488355328 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= ((V 45%nat) - 40) \/ ((V 45%nat) - 40) + 40 <= ((V 2%nat) - 112)) -> (((V 45%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 45%nat) - 40)) -> (((V 45%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 45%nat) - 40)) -> L5.u32_at RSEGS M ((V 45%nat) - 40) 0 ->
  L5.writable RSEGS M ((V 45%nat) - 40) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 45%nat) - 40) <= bv_unsigned a < ((V 45%nat) - 40) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 45%nat) - 40) <= i < ((V 45%nat) - 40) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36c58 M) (st fx' R' 0x36f7c M')
        /\ (forall x, In x KS_bpaH0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 224432
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 45%nat) - 40) 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI6 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_45 := V 45%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 45%nat => Z_to_bv 64 vz_45 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 45%nat => vz_45 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 46%nat. }
  assert (HR: regs_ok E PbpaH0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaH0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaH0.kn0).
  { unfold know_ok, PbpaH0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K16; lia | clear - HV2l HV2r K0l K0r K5 K8 K16; lia | clear - HV2l HV2r K0l K0r K5 K8 K16; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11 K18; lia | clear - HV34l HV34r K6l K6r K8 K11 K18; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | byte_tac ltac:(clear) | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | exactA K20]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaH0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaH0.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_45 - 40) <= bv_unsigned a < (vz_45 - 40) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbpaH0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K14l K14r K16 K17 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaH0.ps0) with 0x36f7c in Hms. change (SR.ps_regs PbpaH0.ps0) with (map (fun i => (i, nth i PbpaH0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaH0.ps0) with PbpaH0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaH0.regs0 PbpaH0.regs_out0 64 KS_bpaH0 KS_bpaH0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaH0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpaH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpaH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpaH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaH1 := LibSegBs_bpaH1_u.
Definition KS_bpaH1 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaH1.regs0 PbpaH1.regs_out0).
Lemma KS_bpaH1_ok : BG.kept_ok 64 PbpaH1.regs0 PbpaH1.regs_out0 KS_bpaH1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaH1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 54%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 58%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 60%nat) -> 140735332483184 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> L5.writable RSEGS M ((V 33%nat) + 8) 2 -> L5.writable RSEGS M ((V 33%nat) + 400) 8 -> 140735332483184 <= (V 34%nat) <= 140737488355320 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 ->
  ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> L5.u8_at RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 40%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 40%nat) + 40) ->
  4096 <= (V 40%nat) <= 140737488355264 -> aligned (V 40%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 40%nat) \/ (V 40%nat) + 40 <= ((V 2%nat) - 112)) -> ((V 40%nat) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 40%nat)) ->
  ((V 40%nat) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 40%nat)) -> L5.u32_at RSEGS M (V 40%nat) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 2) -> ~ (((V 33%nat) + 400) <= bv_unsigned a < ((V 33%nat) + 400) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 2) -> ~ (((V 33%nat) + 400) <= i < ((V 33%nat) + 400) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36c58 M) (st fx' R' 0x36e54 M')
        /\ (forall x, In x KS_bpaH1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 216248
        /\ getr R' (reg 12) = Z_to_bv 64 40
        /\ getr R' (reg 18) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 60%nat)
        /\ (L5.u8_at RSEGS M' ((V 33%nat) + 8) 0 /\ L5.u8_at RSEGS M' (((V 33%nat) + 8) + 1) 1)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 400) (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI17 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 pvzI18 K15 K16 K17 K18 pvzI19 K20 K21 K22 K23 K24 K25 K26 K27 pvzI20 K29 K30 K31 K32 K33.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV40l; move HV40l before pvzI5; pose proof (proj2 pvzI5) as HV40r; move HV40r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV52l; move HV52l before pvzI8; pose proof (proj2 pvzI8) as HV52r; move HV52r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV53l; move HV53l before pvzI9; pose proof (proj2 pvzI9) as HV53r; move HV53r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV54l; move HV54l before pvzI10; pose proof (proj2 pvzI10) as HV54r; move HV54r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV55l; move HV55l before pvzI11; pose proof (proj2 pvzI11) as HV55r; move HV55r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV56l; move HV56l before pvzI12; pose proof (proj2 pvzI12) as HV56r; move HV56r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV57l; move HV57l before pvzI13; pose proof (proj2 pvzI13) as HV57r; move HV57r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV58l; move HV58l before pvzI14; pose proof (proj2 pvzI14) as HV58r; move HV58r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV59l; move HV59l before pvzI15; pose proof (proj2 pvzI15) as HV59r; move HV59r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV60l; move HV60l before pvzI16; pose proof (proj2 pvzI16) as HV60r; move HV60r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K0l; move K0l before pvzI17; pose proof (proj2 pvzI17) as K0r; move K0r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K14l; move K14l before pvzI18; pose proof (proj2 pvzI18) as K14r; move K14r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K19l; move K19l before pvzI19; pose proof (proj2 pvzI19) as K19r; move K19r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K28l; move K28l before pvzI20; pose proof (proj2 pvzI20) as K28r; move K28r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 40%nat => Z_to_bv 64 vz_40 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 40%nat => vz_40 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PbpaH1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaH1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaH1.kn0).
  { unfold know_ok, PbpaH1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | clear - HV2l HV2r K0l K0r K16 K21 K30; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16 K24 K31) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16 K24 K31) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16 K24 K31) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16 K24 K31) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K14l K14r K16 K24 K31; lia | clear - HV33l HV33r K14l K14r K16 K24 K31; lia | clear - HV33l HV33r K14l K14r K16 K24 K31; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16 K24 K31) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K14l K14r K16 K24 K31; lia | clear - HV33l HV33r K14l K14r K16 K24 K31; lia | clear - HV33l HV33r K14l K14r K16 K24 K31; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K19l K19r K21 K24 K32) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K19l K19r K21 K24 K32) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K19l K19r K21 K24 K32) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K19l K19r K21 K24 K32) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K19l K19r K21 K24 K32; lia | clear - HV34l HV34r K19l K19r K21 K24 K32; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16 K24 K31) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K19l K19r K21 K24 K32) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16 K24 K31) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K14l K14r K16 K24 K31; lia | clear - HV33l HV33r K14l K14r K16 K24 K31; lia | byte_tac ltac:(clear) | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16 K24 K31) | evalEk ZA ltac:(clear - HV40l HV40r K28l K28r K30 K31 K32) | clear - HV33l HV33r K14l K14r K16 K24 K31; lia | clear - HV33l HV33r K14l K14r K16 K24 K31; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16 K24 K31) | evalEk ZA ltac:(clear - HV40l HV40r K28l K28r K30 K31 K32) | clear - HV33l HV33r K14l K14r K16 K24 K31; lia | clear - HV33l HV33r K14l K14r K16 K24 K31; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K28l K28r K30 K31 K32) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K28l K28r K30 K31 K32) | clear; lia | exact K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K21 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K28l K28r K30 K31 K32) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K28l K28r K30 K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16 K24 K31) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K28l K28r K30 K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K19l K19r K21 K24 K32) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV40l HV40r K28l K28r K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K28l K28r K30 K31 K32; lia | clear - HV40l HV40r K28l K28r K30 K31 K32; lia | exactA K33]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaH1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaH1.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 2) -> ~ ((vz_33 + 400) <= bv_unsigned a < (vz_33 + 400) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbpaH1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K14l K14r K16 K24 K31) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K14l K14r K16 K24 K31 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K14l K14r K16 K24 K31) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K14l K14r K16 K24 K31 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaH1.ps0) with 0x36e54 in Hms. change (SR.ps_regs PbpaH1.ps0) with (map (fun i => (i, nth i PbpaH1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaH1.ps0) with PbpaH1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaH1.regs0 PbpaH1.regs_out0 64 KS_bpaH1 KS_bpaH1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaH1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbpaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbpaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbpaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbpaH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8x2_of_KWord2a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K14l K14r K16 K24 K31) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K14l K14r K16 K24 K31) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K28l K28r K30 K31 K32) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaH2 := LibSegBs_bpaH2_u.
Definition KS_bpaH2 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaH2.regs0 PbpaH2.regs_out0).
Lemma KS_bpaH2_ok : BG.kept_ok 64 PbpaH2.regs0 PbpaH2.regs_out0 KS_bpaH2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaH2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 140735332483184 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> 140735332483184 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u8_at RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 45%nat) -> 4136 <= (V 45%nat) <= 140737488355328 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= ((V 45%nat) - 40) \/ ((V 45%nat) - 40) + 40 <= ((V 2%nat) - 112)) -> (((V 45%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 45%nat) - 40)) -> (((V 45%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 45%nat) - 40)) -> L5.u32_at RSEGS M ((V 45%nat) - 40) 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36c58 M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_bpaH2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 224464
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 12) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI6 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_45 := V 45%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 45%nat => Z_to_bv 64 vz_45 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 45%nat => vz_45 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 46%nat. }
  assert (HR: regs_ok E PbpaH2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaH2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaH2.kn0).
  { unfold know_ok, PbpaH2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K16; lia | clear - HV2l HV2r K0l K0r K5 K8 K16; lia | clear - HV2l HV2r K0l K0r K5 K8 K16; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11 K18; lia | clear - HV34l HV34r K6l K6r K8 K11 K18; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | byte_tac ltac:(clear) | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | exactA K19]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaH2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaH2.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbpaH2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaH2.ps0) with 0x370d0 in Hms. change (SR.ps_regs PbpaH2.ps0) with (map (fun i => (i, nth i PbpaH2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaH2.ps0) with PbpaH2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaH2.regs0 PbpaH2.regs_out0 64 KS_bpaH2 KS_bpaH2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaH2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbpaH2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpaH2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaH3 := LibSegBs_bpaH3_u.
Definition KS_bpaH3 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaH3.regs0 PbpaH3.regs_out0).
Lemma KS_bpaH3_ok : BG.kept_ok 64 PbpaH3.regs0 PbpaH3.regs_out0 KS_bpaH3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaH3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 140735332483184 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> 140735332483184 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u8_at RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 45%nat) -> 4136 <= (V 45%nat) <= 140737488355328 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= ((V 45%nat) - 40) \/ ((V 45%nat) - 40) + 40 <= ((V 2%nat) - 112)) -> (((V 45%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 45%nat) - 40)) -> (((V 45%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 45%nat) - 40)) -> L5.u32_at RSEGS M ((V 45%nat) - 40) 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36c58 M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_bpaH3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 224588
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 12) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI6 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_45 := V 45%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 45%nat => Z_to_bv 64 vz_45 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 45%nat => vz_45 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 46%nat. }
  assert (HR: regs_ok E PbpaH3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaH3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaH3.kn0).
  { unfold know_ok, PbpaH3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K16; lia | clear - HV2l HV2r K0l K0r K5 K8 K16; lia | clear - HV2l HV2r K0l K0r K5 K8 K16; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11 K18; lia | clear - HV34l HV34r K6l K6r K8 K11 K18; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | byte_tac ltac:(clear) | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | exactA K19]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaH3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaH3.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbpaH3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaH3.ps0) with 0x370d0 in Hms. change (SR.ps_regs PbpaH3.ps0) with (map (fun i => (i, nth i PbpaH3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaH3.ps0) with PbpaH3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaH3.regs0 PbpaH3.regs_out0 64 KS_bpaH3 KS_bpaH3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaH3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpaH3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaH3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpaH3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbpaH3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpaH3.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaH4 := LibSegBs_bpaH4_u.
Definition KS_bpaH4 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaH4.regs0 PbpaH4.regs_out0).
Lemma KS_bpaH4_ok : BG.kept_ok 64 PbpaH4.regs0 PbpaH4.regs_out0 KS_bpaH4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaH4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 140735332483184 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> 140735332483184 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u8_at RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 45%nat) -> 4136 <= (V 45%nat) <= 140737488355328 -> aligned (V 45%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= ((V 45%nat) - 40) \/ ((V 45%nat) - 40) + 40 <= ((V 2%nat) - 112)) -> (((V 45%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 45%nat) - 40)) -> (((V 45%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 45%nat) - 40)) -> L5.u32_at RSEGS M ((V 45%nat) - 40) 4 ->
  L5.u8_at RSEGS M ((V 45%nat) - 16) (V 44%nat) -> 0 <= (V 44%nat) <= 255 -> L5.writable RSEGS M ((V 45%nat) - 40) 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 45%nat) - 40) <= bv_unsigned a < ((V 45%nat) - 40) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 45%nat) - 40) <= i < ((V 45%nat) - 40) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36c58 M) (st fx' R' 0x375ec M')
        /\ (forall x, In x KS_bpaH4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 224676
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 45%nat) - 40) 2).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI7 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 K20 pvzI11 K22.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K21l; move K21l before pvzI11; pose proof (proj2 pvzI11) as K21r; move K21r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 44%nat => vz_44 | 45%nat => vz_45 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 46%nat. }
  assert (HR: regs_ok E PbpaH4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaH4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaH4.kn0).
  { unfold know_ok, PbpaH4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K16; lia | clear - HV2l HV2r K0l K0r K5 K8 K16; lia | clear - HV2l HV2r K0l K0r K5 K8 K16; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11 K18; lia | clear - HV34l HV34r K6l K6r K8 K11 K18; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | byte_tac ltac:(clear) | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | clear - HV33l HV33r K3l K3r K5 K11 K17; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear - HV44l HV44r K21l K21r) | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | byte_tac ltac:(clear - HV44l HV44r K21l K21r) | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | clear - HV45l HV45r K14l K14r K16 K17 K18; lia | exactA K22]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaH4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaH4.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_45 - 40) <= bv_unsigned a < (vz_45 - 40) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbpaH4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K14l K14r K16 K17 K18 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaH4.ps0) with 0x375ec in Hms. change (SR.ps_regs PbpaH4.ps0) with (map (fun i => (i, nth i PbpaH4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaH4.ps0) with PbpaH4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaH4.regs0 PbpaH4.regs_out0 64 KS_bpaH4 KS_bpaH4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaH4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpaH4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaH4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpaH4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpaH4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaH4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbpaH4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV45l HV45r K14l K14r K16 K17 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaR2e := LibSegBs_bpaR2e_u.
Definition KS_bpaR2e : list nat := Eval vm_compute in (BG.kept_list 64 PbpaR2e.regs0 PbpaR2e.regs_out0).
Lemma KS_bpaR2e_ok : BG.kept_ok 64 PbpaR2e.regs0 PbpaR2e.regs_out0 KS_bpaR2e = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaR2e_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 140735332483184 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> 140735332483184 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 45%nat) -> 4136 <= (V 45%nat) <= 140737488355328 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 112) + 112 <= ((V 45%nat) - 40) \/ ((V 45%nat) - 40) + 40 <= ((V 2%nat) - 112)) ->
  (((V 45%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 45%nat) - 40)) -> (((V 45%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 45%nat) - 40)) -> L5.u64_at RSEGS M ((V 45%nat) - 24) (V 43%nat) -> L5.writable RSEGS M ((V 45%nat) - 24) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 45%nat) - 24) <= bv_unsigned a < ((V 45%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 45%nat) - 24) <= i < ((V 45%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36cd0 M) (st fx' R' 0x36ee4 M')
        /\ (forall x, In x KS_bpaR2e -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 224800
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 pvzI7 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 pvzI10 K14 K15 K16 K17 K18 K19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K13l; move K13l before pvzI10; pose proof (proj2 pvzI10) as K13r; move K13r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_45 := V 45%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 43%nat => Z_to_bv 64 vz_43 | 45%nat => Z_to_bv 64 vz_45 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 43%nat => vz_43 | 45%nat => vz_45 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 46%nat. }
  assert (HR: regs_ok E PbpaR2e.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaR2e.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaR2e.kn0).
  { unfold know_ok, PbpaR2e.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11 K17; lia | clear - HV34l HV34r K6l K6r K8 K11 K17; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | clear - HV33l HV33r K3l K3r K5 K11 K16; lia | clear - HV33l HV33r K3l K3r K5 K11 K16; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | exactA K19]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaR2e.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaR2e.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_45 - 24) <= bv_unsigned a < (vz_45 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbpaR2e.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaR2e.ps0) with 0x36ee4 in Hms. change (SR.ps_regs PbpaR2e.ps0) with (map (fun i => (i, nth i PbpaR2e.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaR2e.ps0) with PbpaR2e.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaR2e.regs0 PbpaR2e.regs_out0 64 KS_bpaR2e KS_bpaR2e_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaR2e.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpaR2e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaR2e.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaR2e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaR2e.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpaR2e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbpaR2e.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpaR2e.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaR20 := LibSegBs_bpaR20_u.
Definition KS_bpaR20 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaR20.regs0 PbpaR20.regs_out0).
Lemma KS_bpaR20_ok : BG.kept_ok 64 PbpaR20.regs0 PbpaR20.regs_out0 KS_bpaR20 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaR20_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 140735332483184 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> 140735332483184 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 45%nat) -> 4136 <= (V 45%nat) <= 140737488355328 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 112) + 112 <= ((V 45%nat) - 40) \/ ((V 45%nat) - 40) + 40 <= ((V 2%nat) - 112)) ->
  (((V 45%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 45%nat) - 40)) -> (((V 45%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 45%nat) - 40)) -> L5.u64_at RSEGS M ((V 45%nat) - 24) (V 43%nat) -> L5.writable RSEGS M ((V 45%nat) - 24) 8 ->
  L5.u8_at RSEGS M ((V 2%nat) - 112) (V 46%nat) -> 0 <= (V 46%nat) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 45%nat) - 24) <= bv_unsigned a < ((V 45%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 45%nat) - 24) <= i < ((V 45%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36cd0 M) (st fx' R' 0x3745c M')
        /\ (forall x, In x KS_bpaR20 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 224756
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 35%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 pvzI8 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 pvzI11 K14 K15 K16 K17 K18 K19 K20 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 43%nat => Z_to_bv 64 vz_43 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 43%nat => vz_43 | 45%nat => vz_45 | 46%nat => vz_46 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 47%nat. }
  assert (HR: regs_ok E PbpaR20.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaR20.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaR20.kn0).
  { unfold know_ok, PbpaR20.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11 K17; lia | clear - HV34l HV34r K6l K6r K8 K11 K17; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | clear - HV33l HV33r K3l K3r K5 K11 K16; lia | clear - HV33l HV33r K3l K3r K5 K11 K16; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear - HV46l HV46r K21l K21r) | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | byte_tac ltac:(clear - HV46l HV46r K21l K21r) | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaR20.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaR20.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_45 - 24) <= bv_unsigned a < (vz_45 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbpaR20.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaR20.ps0) with 0x3745c in Hms. change (SR.ps_regs PbpaR20.ps0) with (map (fun i => (i, nth i PbpaR20.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaR20.ps0) with PbpaR20.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaR20.regs0 PbpaR20.regs_out0 64 KS_bpaR20 KS_bpaR20_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaR20.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpaR20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaR20.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaR20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaR20.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpaR20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbpaR20.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpaR20.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaR21 := LibSegBs_bpaR21_u.
Definition KS_bpaR21 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaR21.regs0 PbpaR21.regs_out0).
Lemma KS_bpaR21_ok : BG.kept_ok 64 PbpaR21.regs0 PbpaR21.regs_out0 KS_bpaR21 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaR21_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 140735332483184 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> 140735332483184 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 45%nat) -> 4136 <= (V 45%nat) <= 140737488355328 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 112) + 112 <= ((V 45%nat) - 40) \/ ((V 45%nat) - 40) + 40 <= ((V 2%nat) - 112)) ->
  (((V 45%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 45%nat) - 40)) -> (((V 45%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 45%nat) - 40)) -> L5.u64_at RSEGS M ((V 45%nat) - 24) (V 43%nat) -> L5.writable RSEGS M ((V 45%nat) - 24) 8 ->
  L5.u8_at RSEGS M ((V 2%nat) - 112) (V 46%nat) -> 1 <= (V 46%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 45%nat) - 24) <= bv_unsigned a < ((V 45%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 45%nat) - 24) <= i < ((V 45%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36cd0 M) (st fx' R' 0x37338 M')
        /\ (forall x, In x KS_bpaR21 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 224532
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 35%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 pvzI8 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 pvzI11 K14 K15 K16 K17 K18 K19 K20 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 43%nat => Z_to_bv 64 vz_43 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 43%nat => vz_43 | 45%nat => vz_45 | 46%nat => vz_46 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 47%nat. }
  assert (HR: regs_ok E PbpaR21.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaR21.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaR21.kn0).
  { unfold know_ok, PbpaR21.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11 K17; lia | clear - HV34l HV34r K6l K6r K8 K11 K17; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | clear - HV33l HV33r K3l K3r K5 K11 K16; lia | clear - HV33l HV33r K3l K3r K5 K11 K16; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear - HV46l HV46r K21l K21r) | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | byte_tac ltac:(clear - HV46l HV46r K21l K21r) | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaR21.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaR21.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_45 - 24) <= bv_unsigned a < (vz_45 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbpaR21.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaR21.ps0) with 0x37338 in Hms. change (SR.ps_regs PbpaR21.ps0) with (map (fun i => (i, nth i PbpaR21.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaR21.ps0) with PbpaR21.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaR21.regs0 PbpaR21.regs_out0 64 KS_bpaR21 KS_bpaR21_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaR21.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpaR21.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaR21.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaR21.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaR21.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpaR21.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaR21.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpaR21.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbpaR21.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbpaR21.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaN2 := LibSegBs_bpaN2_u.
Definition KS_bpaN2 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaN2.regs0 PbpaN2.regs_out0).
Lemma KS_bpaN2_ok : BG.kept_ok 64 PbpaN2.regs0 PbpaN2.regs_out0 KS_bpaN2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaN2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 140735332483184 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> 140735332483184 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 45%nat) -> 4136 <= (V 45%nat) <= 140737488355328 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 112) + 112 <= ((V 45%nat) - 40) \/ ((V 45%nat) - 40) + 40 <= ((V 2%nat) - 112)) ->
  (((V 45%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 45%nat) - 40)) -> (((V 45%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 45%nat) - 40)) -> L5.u8_at RSEGS M ((V 2%nat) - 112) (V 46%nat) -> 1 <= (V 46%nat) <= 255 ->
  L5.writable RSEGS M ((V 45%nat) - 40) 4 -> L5.writable RSEGS M ((V 45%nat) - 16) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 45%nat) - 40) <= bv_unsigned a < ((V 45%nat) - 40) + 4) -> ~ (((V 45%nat) - 16) <= bv_unsigned a < ((V 45%nat) - 16) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 45%nat) - 40) <= i < ((V 45%nat) - 40) + 4) -> ~ (((V 45%nat) - 16) <= i < ((V 45%nat) - 16) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36d14 M) (st fx' R' 0x36e08 M')
        /\ (forall x, In x KS_bpaN2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 46%nat)
        /\ L5.u8_at RSEGS M' ((V 45%nat) - 16) (V 46%nat)
        /\ L5.u32_at RSEGS M' ((V 45%nat) - 40) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI7 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 pvzI10 K14 K15 K16 K17 K18 pvzI11 K20 K21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV46l; move HV46l before pvzI6; pose proof (proj2 pvzI6) as HV46r; move HV46r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K13l; move K13l before pvzI10; pose proof (proj2 pvzI10) as K13r; move K13r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K19l; move K19l before pvzI11; pose proof (proj2 pvzI11) as K19r; move K19r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 45%nat => vz_45 | 46%nat => vz_46 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 47%nat. }
  assert (HR: regs_ok E PbpaN2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaN2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaN2.kn0).
  { unfold know_ok, PbpaN2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11 K17; lia | clear - HV34l HV34r K6l K6r K8 K11 K17; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | clear - HV33l HV33r K3l K3r K5 K11 K16; lia | clear - HV33l HV33r K3l K3r K5 K11 K16; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear - HV46l HV46r K19l K19r) | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | byte_tac ltac:(clear - HV46l HV46r K19l K19r) | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | exactA K21]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaN2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaN2.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_45 - 40) <= bv_unsigned a < (vz_45 - 40) + 4) -> ~ ((vz_45 - 16) <= bv_unsigned a < (vz_45 - 16) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbpaN2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaN2.ps0) with 0x36e08 in Hms. change (SR.ps_regs PbpaN2.ps0) with (map (fun i => (i, nth i PbpaN2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaN2.ps0) with PbpaN2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaN2.regs0 PbpaN2.regs_out0 64 KS_bpaN2 KS_bpaN2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaN2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaN2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaN2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpaN2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk' ZA Hag ltac:(clear - HV46l HV46r K19l K19r) | byte_tac ltac:(clear - HV46l HV46r K19l K19r) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaR3e := LibSegBs_bpaR3e_u.
Definition KS_bpaR3e : list nat := Eval vm_compute in (BG.kept_list 64 PbpaR3e.regs0 PbpaR3e.regs_out0).
Lemma KS_bpaR3e_ok : BG.kept_ok 64 PbpaR3e.regs0 PbpaR3e.regs_out0 KS_bpaR3e = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaR3e_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 140735332483184 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> 140735332483184 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 45%nat) -> 4136 <= (V 45%nat) <= 140737488355328 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 112) + 112 <= ((V 45%nat) - 40) \/ ((V 45%nat) - 40) + 40 <= ((V 2%nat) - 112)) ->
  (((V 45%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 45%nat) - 40)) -> (((V 45%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 45%nat) - 40)) -> L5.u64_at RSEGS M ((V 45%nat) - 24) (V 43%nat) -> L5.writable RSEGS M ((V 45%nat) - 24) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 45%nat) - 24) <= bv_unsigned a < ((V 45%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 45%nat) - 24) <= i < ((V 45%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36d4c M) (st fx' R' 0x36ee4 M')
        /\ (forall x, In x KS_bpaR3e -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 224800
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 pvzI7 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 pvzI10 K14 K15 K16 K17 K18 K19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K13l; move K13l before pvzI10; pose proof (proj2 pvzI10) as K13r; move K13r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_45 := V 45%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 43%nat => Z_to_bv 64 vz_43 | 45%nat => Z_to_bv 64 vz_45 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 43%nat => vz_43 | 45%nat => vz_45 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 46%nat. }
  assert (HR: regs_ok E PbpaR3e.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaR3e.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaR3e.kn0).
  { unfold know_ok, PbpaR3e.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11 K17; lia | clear - HV34l HV34r K6l K6r K8 K11 K17; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | clear - HV33l HV33r K3l K3r K5 K11 K16; lia | clear - HV33l HV33r K3l K3r K5 K11 K16; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | exactA K19]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaR3e.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaR3e.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_45 - 24) <= bv_unsigned a < (vz_45 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbpaR3e.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaR3e.ps0) with 0x36ee4 in Hms. change (SR.ps_regs PbpaR3e.ps0) with (map (fun i => (i, nth i PbpaR3e.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaR3e.ps0) with PbpaR3e.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaR3e.regs0 PbpaR3e.regs_out0 64 KS_bpaR3e KS_bpaR3e_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaR3e.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpaR3e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaR3e.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaR3e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaR3e.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpaR3e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbpaR3e.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpaR3e.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaR30 := LibSegBs_bpaR30_u.
Definition KS_bpaR30 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaR30.regs0 PbpaR30.regs_out0).
Lemma KS_bpaR30_ok : BG.kept_ok 64 PbpaR30.regs0 PbpaR30.regs_out0 KS_bpaR30 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaR30_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 140735332483184 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> 140735332483184 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 45%nat) -> 4136 <= (V 45%nat) <= 140737488355328 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 112) + 112 <= ((V 45%nat) - 40) \/ ((V 45%nat) - 40) + 40 <= ((V 2%nat) - 112)) ->
  (((V 45%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 45%nat) - 40)) -> (((V 45%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 45%nat) - 40)) -> L5.u64_at RSEGS M ((V 45%nat) - 24) (V 43%nat) -> L5.writable RSEGS M ((V 45%nat) - 24) 8 ->
  L5.u8_at RSEGS M ((V 2%nat) - 112) (V 46%nat) -> 0 <= (V 46%nat) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 45%nat) - 24) <= bv_unsigned a < ((V 45%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 45%nat) - 24) <= i < ((V 45%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36d4c M) (st fx' R' 0x37db4 M')
        /\ (forall x, In x KS_bpaR30 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 224776
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 35%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 pvzI8 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 pvzI11 K14 K15 K16 K17 K18 K19 K20 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 43%nat => Z_to_bv 64 vz_43 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 43%nat => vz_43 | 45%nat => vz_45 | 46%nat => vz_46 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 47%nat. }
  assert (HR: regs_ok E PbpaR30.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaR30.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaR30.kn0).
  { unfold know_ok, PbpaR30.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11 K17; lia | clear - HV34l HV34r K6l K6r K8 K11 K17; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | clear - HV33l HV33r K3l K3r K5 K11 K16; lia | clear - HV33l HV33r K3l K3r K5 K11 K16; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear - HV46l HV46r K21l K21r) | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | byte_tac ltac:(clear - HV46l HV46r K21l K21r) | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaR30.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaR30.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_45 - 24) <= bv_unsigned a < (vz_45 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbpaR30.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaR30.ps0) with 0x37db4 in Hms. change (SR.ps_regs PbpaR30.ps0) with (map (fun i => (i, nth i PbpaR30.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaR30.ps0) with PbpaR30.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaR30.regs0 PbpaR30.regs_out0 64 KS_bpaR30 KS_bpaR30_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaR30.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpaR30.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaR30.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaR30.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaR30.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpaR30.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbpaR30.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpaR30.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaR31 := LibSegBs_bpaR31_u.
Definition KS_bpaR31 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaR31.regs0 PbpaR31.regs_out0).
Lemma KS_bpaR31_ok : BG.kept_ok 64 PbpaR31.regs0 PbpaR31.regs_out0 KS_bpaR31 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaR31_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 140735332483184 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> 140735332483184 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 45%nat) -> 4136 <= (V 45%nat) <= 140737488355328 -> aligned (V 45%nat) 8 -> (((V 2%nat) - 112) + 112 <= ((V 45%nat) - 40) \/ ((V 45%nat) - 40) + 40 <= ((V 2%nat) - 112)) ->
  (((V 45%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 45%nat) - 40)) -> (((V 45%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 45%nat) - 40)) -> L5.u64_at RSEGS M ((V 45%nat) - 24) (V 43%nat) -> L5.writable RSEGS M ((V 45%nat) - 24) 8 ->
  L5.u8_at RSEGS M ((V 2%nat) - 112) (V 46%nat) -> 1 <= (V 46%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 45%nat) - 24) <= bv_unsigned a < ((V 45%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 45%nat) - 24) <= i < ((V 45%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36d4c M) (st fx' R' 0x37338 M')
        /\ (forall x, In x KS_bpaR31 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 224656
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 (V 35%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 pvzI8 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 pvzI11 K14 K15 K16 K17 K18 K19 K20 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K13l; move K13l before pvzI11; pose proof (proj2 pvzI11) as K13r; move K13r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 43%nat => Z_to_bv 64 vz_43 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 43%nat => vz_43 | 45%nat => vz_45 | 46%nat => vz_46 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 47%nat. }
  assert (HR: regs_ok E PbpaR31.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaR31.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaR31.kn0).
  { unfold know_ok, PbpaR31.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11 K17; lia | clear - HV34l HV34r K6l K6r K8 K11 K17; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | clear - HV33l HV33r K3l K3r K5 K11 K16; lia | clear - HV33l HV33r K3l K3r K5 K11 K16; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | clear - HV45l HV45r K13l K13r K15 K16 K17; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8 K15) | evalEk ZA ltac:(clear - HV46l HV46r K21l K21r) | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | clear - HV2l HV2r K0l K0r K5 K8 K15; lia | byte_tac ltac:(clear - HV46l HV46r K21l K21r) | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaR31.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaR31.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_45 - 24) <= bv_unsigned a < (vz_45 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbpaR31.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K13l K13r K15 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K13l K13r K15 K16 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaR31.ps0) with 0x37338 in Hms. change (SR.ps_regs PbpaR31.ps0) with (map (fun i => (i, nth i PbpaR31.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaR31.ps0) with PbpaR31.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaR31.regs0 PbpaR31.regs_out0 64 KS_bpaR31 KS_bpaR31_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaR31.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpaR31.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaR31.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaR31.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaR31.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpaR31.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaR31.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpaR31.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbpaR31.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbpaR31.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaN3 := LibSegBs_bpaN3_u.
Definition KS_bpaN3 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaN3.regs0 PbpaN3.regs_out0).
Lemma KS_bpaN3_ok : BG.kept_ok 64 PbpaN3.regs0 PbpaN3.regs_out0 KS_bpaN3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaN3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 140735332483184 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> 140735332483184 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 112)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  L5.u8_at RSEGS M ((V 2%nat) - 112) (V 46%nat) -> 1 <= (V 46%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36d90 M) (st fx' R' 0x375ec M')
        /\ (forall x, In x KS_bpaN3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 224676
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 35%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI6 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV46l; move HV46l before pvzI5; pose proof (proj2 pvzI5) as HV46r; move HV46r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_46 := V 46%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 46%nat => Z_to_bv 64 vz_46 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 46%nat => vz_46 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 47%nat. }
  assert (HR: regs_ok E PbpaN3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaN3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaN3.kn0).
  { unfold know_ok, PbpaN3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K8; lia | clear - HV2l HV2r K0l K0r K5 K8; lia | clear - HV2l HV2r K0l K0r K5 K8; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K6l K6r K8 K11; lia | clear - HV34l HV34r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K8) | evalEk ZA ltac:(clear - HV46l HV46r K13l K13r) | clear - HV2l HV2r K0l K0r K5 K8; lia | clear - HV2l HV2r K0l K0r K5 K8; lia | byte_tac ltac:(clear - HV46l HV46r K13l K13r) | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaN3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaN3.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbpaN3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaN3.ps0) with 0x375ec in Hms. change (SR.ps_regs PbpaN3.ps0) with (map (fun i => (i, nth i PbpaN3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaN3.ps0) with PbpaN3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaN3.regs0 PbpaN3.regs_out0 64 KS_bpaN3 KS_bpaN3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaN3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpaN3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaN3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaN3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaN3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbpaN3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaN3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbpaN3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbpaN3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbpaN3.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaX0 := LibSegBs_bpaX0_u.
Definition KS_bpaX0 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaX0.regs0 PbpaX0.regs_out0).
Lemma KS_bpaX0_ok : BG.kept_ok 64 PbpaX0.regs0 PbpaX0.regs_out0 KS_bpaX0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaX0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> 140735332483184 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> L5.u8_at RSEGS M ((V 33%nat) + 9) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36e08 M) (st fx' R' 0x36c58 M')
        /\ (forall x, In x KS_bpaX0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI5 K1 K2 pvzI6 K4 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PbpaX0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaX0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaX0.kn0).
  { unfold know_ok, PbpaX0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | byte_tac ltac:(clear) | exactA K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaX0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaX0.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbpaX0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaX0.ps0) with 0x36c58 in Hms. change (SR.ps_regs PbpaX0.ps0) with (map (fun i => (i, nth i PbpaX0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaX0.ps0) with PbpaX0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaX0.regs0 PbpaX0.regs_out0 64 KS_bpaX0 KS_bpaX0_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PbpaX0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaX0.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaX1 := LibSegBs_bpaX1_u.
Definition KS_bpaX1 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaX1.regs0 PbpaX1.regs_out0).
Lemma KS_bpaX1_ok : BG.kept_ok 64 PbpaX1.regs0 PbpaX1.regs_out0 KS_bpaX1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaX1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 54%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 58%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 60%nat) -> 140735332483184 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> L5.u8_at RSEGS M ((V 33%nat) + 9) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36e08 M) (st fx' R' 0x36e54 M')
        /\ (forall x, In x KS_bpaX1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 60%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI16 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 pvzI17 K15 K16 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV52l; move HV52l before pvzI7; pose proof (proj2 pvzI7) as HV52r; move HV52r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV53l; move HV53l before pvzI8; pose proof (proj2 pvzI8) as HV53r; move HV53r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV54l; move HV54l before pvzI9; pose proof (proj2 pvzI9) as HV54r; move HV54r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV55l; move HV55l before pvzI10; pose proof (proj2 pvzI10) as HV55r; move HV55r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV56l; move HV56l before pvzI11; pose proof (proj2 pvzI11) as HV56r; move HV56r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV57l; move HV57l before pvzI12; pose proof (proj2 pvzI12) as HV57r; move HV57r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV58l; move HV58l before pvzI13; pose proof (proj2 pvzI13) as HV58r; move HV58r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV59l; move HV59l before pvzI14; pose proof (proj2 pvzI14) as HV59r; move HV59r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV60l; move HV60l before pvzI15; pose proof (proj2 pvzI15) as HV60r; move HV60r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K14l; move K14l before pvzI17; pose proof (proj2 pvzI17) as K14r; move K14r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PbpaX1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaX1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaX1.kn0).
  { unfold know_ok, PbpaX1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K14l K14r K16; lia | clear - HV33l HV33r K14l K14r K16; lia | byte_tac ltac:(clear) | exactA K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaX1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaX1.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbpaX1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaX1.ps0) with 0x36e54 in Hms. change (SR.ps_regs PbpaX1.ps0) with (map (fun i => (i, nth i PbpaX1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaX1.ps0) with PbpaX1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaX1.regs0 PbpaX1.regs_out0 64 KS_bpaX1 KS_bpaX1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaX1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpaX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaX1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpaX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaX1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpaX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaX1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpaX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaX1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbpaX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaX1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpaX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaX1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpaX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaX1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpaX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaX1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpaX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaX1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbpaX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaX1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbpaX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaX1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbpaX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbpaX1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbpaX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaJ74 := LibSegBs_bpaJ74_u.
Definition KS_bpaJ74 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaJ74.regs0 PbpaJ74.regs_out0).
Lemma KS_bpaJ74_ok : BG.kept_ok 64 PbpaJ74.regs0 PbpaJ74.regs_out0 KS_bpaJ74 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaJ74_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36cb0 M) (st fx' R' 0x36e08 M')
        /\ (forall x, In x KS_bpaJ74 -> getr R' (reg x) = getr R (reg x))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI5 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PbpaJ74.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaJ74.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaJ74.kn0).
  { unfold know_ok, PbpaJ74.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaJ74.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaJ74.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbpaJ74.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaJ74.ps0) with 0x36e08 in Hms. change (SR.ps_regs PbpaJ74.ps0) with (map (fun i => (i, nth i PbpaJ74.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaJ74.ps0) with PbpaJ74.cells0 in Hcells.
  split. { exact Hms. }
  intros j Hj. apply (BG.kept_regs E E' R R' PbpaJ74.regs0 PbpaJ74.regs_out0 64 KS_bpaJ74 KS_bpaJ74_ok HR Hag Hregs j Hj). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaJ2c := LibSegBs_bpaJ2c_u.
Definition KS_bpaJ2c : list nat := Eval vm_compute in (BG.kept_list 64 PbpaJ2c.regs0 PbpaJ2c.regs_out0).
Lemma KS_bpaJ2c_ok : BG.kept_ok 64 PbpaJ2c.regs0 PbpaJ2c.regs_out0 KS_bpaJ2c = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaJ2c_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36da4 M) (st fx' R' 0x36e08 M')
        /\ (forall x, In x KS_bpaJ2c -> getr R' (reg x) = getr R (reg x))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI5 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PbpaJ2c.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaJ2c.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaJ2c.kn0).
  { unfold know_ok, PbpaJ2c.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaJ2c.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaJ2c.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbpaJ2c.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaJ2c.ps0) with 0x36e08 in Hms. change (SR.ps_regs PbpaJ2c.ps0) with (map (fun i => (i, nth i PbpaJ2c.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaJ2c.ps0) with PbpaJ2c.cells0 in Hcells.
  split. { exact Hms. }
  intros j Hj. apply (BG.kept_regs E E' R R' PbpaJ2c.regs0 PbpaJ2c.regs_out0 64 KS_bpaJ2c KS_bpaJ2c_ok HR Hag Hregs j Hj). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaJ68 := LibSegBs_bpaJ68_u.
Definition KS_bpaJ68 : list nat := Eval vm_compute in (BG.kept_list 64 PbpaJ68.regs0 PbpaJ68.regs_out0).
Lemma KS_bpaJ68_ok : BG.kept_ok 64 PbpaJ68.regs0 PbpaJ68.regs_out0 KS_bpaJ68 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaJ68_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36df4 M) (st fx' R' 0x36e08 M')
        /\ (forall x, In x KS_bpaJ68 -> getr R' (reg x) = getr R (reg x))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI5 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PbpaJ68.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaJ68.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaJ68.kn0).
  { unfold know_ok, PbpaJ68.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaJ68.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaJ68.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbpaJ68.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaJ68.ps0) with 0x36e08 in Hms. change (SR.ps_regs PbpaJ68.ps0) with (map (fun i => (i, nth i PbpaJ68.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaJ68.ps0) with PbpaJ68.cells0 in Hcells.
  split. { exact Hms. }
  intros j Hj. apply (BG.kept_regs E E' R R' PbpaJ68.regs0 PbpaJ68.regs_out0 64 KS_bpaJ68 KS_bpaJ68_ok HR Hag Hregs j Hj). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbpaME := LibSegBs_bpaME_u.
Definition KS_bpaME : list nat := Eval vm_compute in (BG.kept_list 64 PbpaME.regs0 PbpaME.regs_out0).
Lemma KS_bpaME_ok : BG.kept_ok 64 PbpaME.regs0 PbpaME.regs_out0 KS_bpaME = true. Proof. vm_compute. reflexivity. Qed.
Lemma bpaME_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 21) = Z_to_bv 64 40 -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 2 -> getr R (reg 24) = Z_to_bv 64 79632 -> getr R (reg 25) = Z_to_bv 64 256 ->
  140735332483184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 54%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 58%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 60%nat) -> 140735332483184 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 112)) -> L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36e20 M) (st fx' R' 0x36e54 M')
        /\ (forall x, In x KS_bpaME -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 60%nat)
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI16 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 pvzI17 K15 K16 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV52l; move HV52l before pvzI7; pose proof (proj2 pvzI7) as HV52r; move HV52r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV53l; move HV53l before pvzI8; pose proof (proj2 pvzI8) as HV53r; move HV53r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV54l; move HV54l before pvzI9; pose proof (proj2 pvzI9) as HV54r; move HV54r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV55l; move HV55l before pvzI10; pose proof (proj2 pvzI10) as HV55r; move HV55r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV56l; move HV56l before pvzI11; pose proof (proj2 pvzI11) as HV56r; move HV56r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV57l; move HV57l before pvzI12; pose proof (proj2 pvzI12) as HV57r; move HV57r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV58l; move HV58l before pvzI13; pose proof (proj2 pvzI13) as HV58r; move HV58r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV59l; move HV59l before pvzI14; pose proof (proj2 pvzI14) as HV59r; move HV59r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV60l; move HV60l before pvzI15; pose proof (proj2 pvzI15) as HV60r; move HV60r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K14l; move K14l before pvzI17; pose proof (proj2 pvzI17) as K14r; move K14r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PbpaME.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbpaME.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbpaME.kn0).
  { unfold know_ok, PbpaME.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K16; lia | clear - HV2l HV2r K0l K0r K16; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K14l K14r K16) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K14l K14r K16; lia | clear - HV33l HV33r K14l K14r K16; lia | clear - HV33l HV33r K14l K14r K16; lia | exactA K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbpaME.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbpaME.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbpaME.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K14l K14r K16) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K14l K14r K16 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbpaME.ps0) with 0x36e54 in Hms. change (SR.ps_regs PbpaME.ps0) with (map (fun i => (i, nth i PbpaME.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbpaME.ps0) with PbpaME.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbpaME.regs0 PbpaME.regs_out0 64 KS_bpaME KS_bpaME_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbpaME.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbpaME.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaME.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbpaME.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaME.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbpaME.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaME.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbpaME.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaME.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbpaME.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaME.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbpaME.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaME.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbpaME.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaME.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbpaME.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaME.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbpaME.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaME.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbpaME.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaME.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbpaME.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbpaME.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbpaME.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K14l K14r K16) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PNSPAP.
