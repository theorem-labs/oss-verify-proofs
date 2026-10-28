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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_bhaC_b LibSegBa_bhaD_b LibSegBa_bhaE_b LibSegBa_bhaF_b LibSegBa_bhaG_b LibSegBa_bhaH_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAHP2.
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
Module PbhaC := LibSegBa_bhaC_b.
Definition KS_bhaC : list nat := Eval vm_compute in (BG.kept_list 64 PbhaC.regs0 PbhaC.regs_out0).
Lemma KS_bhaC_ok : BG.kept_ok 64 PbhaC.regs0 PbhaC.regs_out0 KS_bhaC = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhaC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (V 33%nat) -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  140735332487360 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 40%nat) <= 140737488353280 ->
  aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 2048 -> L5.writable RSEGS M (V 40%nat) 2048 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 2048 <= 2147446784) ->
  L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 256 -> L5.u64_at RSEGS M ((V 40%nat) + 2040) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 2048 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 128) + 144 <= (V 40%nat) \/ (V 40%nat) + 2048 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 144 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 40%nat) / 8) + 2147450892) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450892) + 34) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 40%nat) / 8) + 2147450892) <= i < (((V 40%nat) / 8) + 2147450892) + 34) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xa82ac M) (st fx' R' 0xa8b74 M')
        /\ (forall x, In x KS_bhaC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 688964
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 96)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 8
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450925) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450924) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450919) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450918) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450917) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450916) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450923) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450922) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450921) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450920) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450911) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450910) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450909) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450908) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450915) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450914) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450913) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450912) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450903) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450902) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450901) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450900) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450907) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450906) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450905) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450904) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450895) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450894) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450893) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450892) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450899) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450898) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450897) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450896) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G1 G2 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 K8 K9 pvzI9 K11 K12 K13 K14 K15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV58l; move HV58l before pvzI6; pose proof (proj2 pvzI6) as HV58r; move HV58r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K10l; move K10l before pvzI9; pose proof (proj2 pvzI9) as K10r; move K10r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_58 := V 58%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 58%nat => Z_to_bv 64 vz_58 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 40%nat => vz_40 | 41%nat => vz_41 | 58%nat => vz_58 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PbhaC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhaC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhaC.kn0).
  { unfold know_ok, PbhaC.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhaC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhaC.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((vz_40 / 8) + 2147450892) <= bv_unsigned a < ((vz_40 / 8) + 2147450892) + 34) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbhaC.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhaC.ps0) with 0xa8b74 in Hms. change (SR.ps_regs PbhaC.ps0) with (map (fun i => (i, nth i PbhaC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhaC.ps0) with PbhaC.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhaC.regs0 PbhaC.regs_out0 64 KS_bhaC KS_bhaC_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhaC.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhaC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaC.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhaC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaC.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhaC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaC.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhaC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhaD := LibSegBa_bhaD_b.
Definition KS_bhaD : list nat := Eval vm_compute in (BG.kept_list 64 PbhaD.regs0 PbhaD.regs_out0).
Lemma KS_bhaD_ok : BG.kept_ok 64 PbhaD.regs0 PbhaD.regs_out0 KS_bhaD = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhaD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 (V 33%nat) -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  140735332487360 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 40%nat) <= 140737488353280 ->
  aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 2048 -> L5.writable RSEGS M (V 40%nat) 2048 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 2048 <= 2147446784) ->
  L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 256 -> L5.u64_at RSEGS M ((V 40%nat) + 2040) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 2048 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 128) + 144 <= (V 40%nat) \/ (V 40%nat) + 2048 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 144 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 40%nat) + 432) <= bv_unsigned a < ((V 40%nat) + 432) + 8) -> ~ (((V 40%nat) + 960) <= bv_unsigned a < ((V 40%nat) + 960) + 24) -> ~ ((((V 40%nat) / 8) + 2147450934) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450934) + 1) -> ~ ((((V 40%nat) / 8) + 2147450938) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450938) + 53) -> ~ ((((V 40%nat) / 8) + 2147451000) <= bv_unsigned a < (((V 40%nat) / 8) + 2147451000) + 3) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 40%nat) + 432) <= i < ((V 40%nat) + 432) + 8) -> ~ (((V 40%nat) + 960) <= i < ((V 40%nat) + 960) + 24) -> ~ ((((V 40%nat) / 8) + 2147450934) <= i < (((V 40%nat) / 8) + 2147450934) + 1) -> ~ ((((V 40%nat) / 8) + 2147450938) <= i < (((V 40%nat) / 8) + 2147450938) + 53) -> ~ ((((V 40%nat) / 8) + 2147451000) <= i < (((V 40%nat) / 8) + 2147451000) + 3) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xa8344 M) (st fx' R' 0xac78c M')
        /\ (forall x, In x KS_bhaD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 689268
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 464)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 96)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 960)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 14) = Z_to_bv 64 1251456
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 40%nat) + 464)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 40%nat) + 432)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 976) 1024
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 980) 0
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 968) 1251840
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 960) 1251800
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451002) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451001) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451000) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450990) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450989) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450988) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450987) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450986) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450981) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450980) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450979) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450978) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450985) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450984) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450983) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450982) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450973) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450972) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450971) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450970) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450977) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450976) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450975) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450974) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450965) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450964) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450963) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450962) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450969) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450968) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450967) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450966) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450957) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450956) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450955) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450954) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450961) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450960) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450959) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450958) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450949) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450948) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450947) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450946) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450953) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450952) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450951) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450950) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450941) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450940) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450939) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450938) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450945) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450944) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450943) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450942) 0
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 432) 1251456
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450934) 0
        /\ L5.defined M' (V 40%nat) 432
        /\ L5.defined M' ((V 40%nat) + 440) 520
        /\ L5.defined M' ((V 40%nat) + 984) 1064).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G1 G2 G9 G18 G19 G20 G21 G22 G23 G24 G25 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 K8 K9 pvzI9 K11 K12 K13 K14 K15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV58l; move HV58l before pvzI6; pose proof (proj2 pvzI6) as HV58r; move HV58r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K10l; move K10l before pvzI9; pose proof (proj2 pvzI9) as K10r; move K10r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_58 := V 58%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 58%nat => Z_to_bv 64 vz_58 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 40%nat => vz_40 | 41%nat => vz_41 | 58%nat => vz_58 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PbhaD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhaD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhaD.kn0).
  { unfold know_ok, PbhaD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhaD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhaD.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_40 + 432) <= bv_unsigned a < (vz_40 + 432) + 8) -> ~ ((vz_40 + 960) <= bv_unsigned a < (vz_40 + 960) + 24) -> ~ (((vz_40 / 8) + 2147450934) <= bv_unsigned a < ((vz_40 / 8) + 2147450934) + 1) -> ~ (((vz_40 / 8) + 2147450938) <= bv_unsigned a < ((vz_40 / 8) + 2147450938) + 53) -> ~ (((vz_40 / 8) + 2147451000) <= bv_unsigned a < ((vz_40 / 8) + 2147451000) + 3) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4. apply Hfr. unfold PbhaD.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 Hn4; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhaD.ps0) with 0xac78c in Hms. change (SR.ps_regs PbhaD.ps0) with (map (fun i => (i, nth i PbhaD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhaD.ps0) with PbhaD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhaD.regs0 PbhaD.regs_out0 64 KS_bhaD KS_bhaD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhaD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhaD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhaD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaD.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhaD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaD.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhaD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaD.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbhaD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaD.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbhaD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaD.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbhaD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaD.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbhaD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 36%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 37%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 38%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 39%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 40%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 41%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 42%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 43%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 44%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 45%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 46%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 47%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 48%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 49%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 50%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 51%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 52%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 53%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 54%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 55%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 56%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 57%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 58%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 59%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 60%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 61%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 62%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 63%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 64%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhaE := LibSegBa_bhaE_b.
Definition KS_bhaE : list nat := Eval vm_compute in (BG.kept_list 64 PbhaE.regs0 PbhaE.regs_out0).
Lemma KS_bhaE_ok : BG.kept_ok 64 PbhaE.regs0 PbhaE.regs_out0 KS_bhaE = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhaE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 22) = Z_to_bv 64 ((V 40%nat) + 464) -> getr R (reg 23) = Z_to_bv 64 (V 33%nat) -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 432) ->
  140735332487360 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 40%nat) <= 140737488353280 ->
  aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 2048 -> L5.writable RSEGS M (V 40%nat) 2048 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 2048 <= 2147446784) ->
  L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 256 -> L5.u64_at RSEGS M ((V 40%nat) + 2040) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 2048 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 128) + 144 <= (V 40%nat) \/ (V 40%nat) + 2048 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 144 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 128)) ->
  L5KA.zeros_at M (((V 40%nat) / 8) + 2147450990) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 40%nat) + 880) <= bv_unsigned a < ((V 40%nat) + 880) + 8) -> ~ (((V 40%nat) + 1024) <= bv_unsigned a < ((V 40%nat) + 1024) + 4) -> ~ ((((V 40%nat) / 8) + 2147451000) <= bv_unsigned a < (((V 40%nat) / 8) + 2147451000) + 3) -> ~ ((((V 40%nat) / 8) + 2147451008) <= bv_unsigned a < (((V 40%nat) / 8) + 2147451008) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 40%nat) + 880) <= i < ((V 40%nat) + 880) + 8) -> ~ (((V 40%nat) + 1024) <= i < ((V 40%nat) + 1024) + 4) -> ~ ((((V 40%nat) / 8) + 2147451000) <= i < (((V 40%nat) / 8) + 2147451000) + 3) -> ~ ((((V 40%nat) / 8) + 2147451008) <= i < (((V 40%nat) / 8) + 2147451008) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xa8474 M) (st fx' R' 0xd950c M')
        /\ (forall x, In x KS_bhaE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 689328
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 880)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 40%nat) + 1024)
        /\ getr R' (reg 26) = Z_to_bv 64 18446744073709551608
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 1024) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451008) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451002) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451001) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451000) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451009) 0
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 880) ((V 40%nat) + 432)
        /\ L5.defined M' (V 40%nat) 880
        /\ L5.defined M' ((V 40%nat) + 888) 136
        /\ L5.defined M' ((V 40%nat) + 1028) 1020).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G1 G2 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI6 K1 K2 pvzI7 K4 K5 K6 K7 K8 K9 pvzI8 K11 K12 K13 K14 K15 K16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV58l; move HV58l before pvzI5; pose proof (proj2 pvzI5) as HV58r; move HV58r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K10l; move K10l before pvzI8; pose proof (proj2 pvzI8) as K10r; move K10r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_58 := V 58%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 58%nat => Z_to_bv 64 vz_58 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 40%nat => vz_40 | 41%nat => vz_41 | 58%nat => vz_58 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PbhaE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhaE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhaE.kn0).
  { unfold know_ok, PbhaE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K16]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhaE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhaE.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_40 + 880) <= bv_unsigned a < (vz_40 + 880) + 8) -> ~ ((vz_40 + 1024) <= bv_unsigned a < (vz_40 + 1024) + 4) -> ~ (((vz_40 / 8) + 2147451000) <= bv_unsigned a < ((vz_40 / 8) + 2147451000) + 3) -> ~ (((vz_40 / 8) + 2147451008) <= bv_unsigned a < ((vz_40 / 8) + 2147451008) + 2) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbhaE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhaE.ps0) with 0xd950c in Hms. change (SR.ps_regs PbhaE.ps0) with (map (fun i => (i, nth i PbhaE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhaE.ps0) with PbhaE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhaE.regs0 PbhaE.regs_out0 64 KS_bhaE KS_bhaE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhaE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhaE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhaE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaE.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhaE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaE.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbhaE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaE.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbhaE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhaF := LibSegBa_bhaF_b.
Definition KS_bhaF : list nat := Eval vm_compute in (BG.kept_list 64 PbhaF.regs0 PbhaF.regs_out0).
Lemma KS_bhaF_ok : BG.kept_ok 64 PbhaF.regs0 PbhaF.regs_out0 KS_bhaF = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhaF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 22) = Z_to_bv 64 ((V 40%nat) + 464) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 1024) -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 18446744073709551608 ->
  140735332487360 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 4096 <= (V 40%nat) <= 140737488353280 ->
  aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 2048 -> L5.writable RSEGS M (V 40%nat) 2048 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 2048 <= 2147446784) ->
  L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 256 -> L5.u64_at RSEGS M ((V 40%nat) + 2040) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 2048 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 160) + 176 <= (V 40%nat) \/ (V 40%nat) + 2048 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 176 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 160)) ->
  L5.u64_at RSEGS M 1275072 1309752 -> L5.u64_at RSEGS M 1309752 2147450880 -> (65536 + 6840320 <= (V 40%nat) \/ (V 40%nat) + 2048 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 40%nat) + 1032) <= bv_unsigned a < ((V 40%nat) + 1032) + 8) -> ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 40%nat) + 1032) <= i < ((V 40%nat) + 1032) + 8) -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xa84b0 M) (st fx' R' 0xadb68 M')
        /\ (forall x, In x KS_bhaF -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 691780
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 40%nat) + 1024)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 40%nat) + 464)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 464)
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 18) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 1032) (bv_unsigned (getr R (reg 10)))
        /\ L5.defined M' (V 40%nat) 1032
        /\ L5.defined M' ((V 40%nat) + 1040) 1008
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) ((V 2%nat) - 128)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 689344).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G1 G2 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI5 K1 K2 pvzI6 K4 K5 K6 K7 K8 K9 pvzI7 K11 K12 K13 K14 K15 K16 K17 K18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV41l; move HV41l before pvzI3; pose proof (proj2 pvzI3) as HV41r; move HV41r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV58l; move HV58l before pvzI4; pose proof (proj2 pvzI4) as HV58r; move HV58r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K10l; move K10l before pvzI7; pose proof (proj2 pvzI7) as K10r; move K10r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_58 := V 58%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 58%nat => Z_to_bv 64 vz_58 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 41%nat => vz_41 | 58%nat => vz_58 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PbhaF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhaF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhaF.kn0).
  { unfold know_ok, PbhaF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14 K18) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14 K18) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14 K18) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 K18; lia | clear - HV40l HV40r K3l K3r K7 K13 K14 K18; lia | clear - HV40l HV40r K3l K3r K7 K13 K14 K18; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14 K18) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 K18; lia | clear - HV40l HV40r K3l K3r K7 K13 K14 K18; lia | clear - HV40l HV40r K3l K3r K7 K13 K14 K18; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14 K18) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14 K18) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 K18; lia | clear - HV40l HV40r K3l K3r K7 K13 K14 K18; lia | clear - HV40l HV40r K3l K3r K7 K13 K14 K18; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14 K18) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | clear - HV40l HV40r K3l K3r K7 K13 K14 K18; lia | clear - HV40l HV40r K3l K3r K7 K13 K14 K18; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14 K18) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhaF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhaF.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_40 + 1032) <= bv_unsigned a < (vz_40 + 1032) + 8) -> ~ ((vz_2 - 160) <= bv_unsigned a < (vz_2 - 160) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbhaF.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 K18 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhaF.ps0) with 0xadb68 in Hms. change (SR.ps_regs PbhaF.ps0) with (map (fun i => (i, nth i PbhaF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhaF.ps0) with PbhaF.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhaF.regs0 PbhaF.regs_out0 64 KS_bhaF KS_bhaF_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhaF.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhaF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaF.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbhaF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaF.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbhaF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaF.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbhaF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaF.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhaF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaF.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhaF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaF.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbhaF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14 K18) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhaG := LibSegBa_bhaG_b.
Definition KS_bhaG : list nat := Eval vm_compute in (BG.kept_list 64 PbhaG.regs0 PbhaG.regs_out0).
Lemma KS_bhaG_ok : BG.kept_ok 64 PbhaG.regs0 PbhaG.regs_out0 KS_bhaG = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhaG_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 ((V 40%nat) + 1024) -> getr R (reg 9) = Z_to_bv 64 ((V 40%nat) + 464) -> getr R (reg 18) = Z_to_bv 64 2147450880 -> getr R (reg 19) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 22) = Z_to_bv 64 ((V 40%nat) + 464) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 1024) -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 18446744073709551608 ->
  140735332487360 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 4096 <= (V 40%nat) <= 140737488353280 ->
  aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 2048 -> L5.writable RSEGS M (V 40%nat) 2048 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 2048 <= 2147446784) ->
  L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 256 -> L5.u64_at RSEGS M ((V 40%nat) + 2040) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 2048 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 160) + 176 <= (V 40%nat) \/ (V 40%nat) + 2048 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 176 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 160)) ->
  L5.u64_at RSEGS M ((V 40%nat) + 880) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) ((V 2%nat) - 128) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 8%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) 689344 -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450990) 1 -> 4096 <= (V 35%nat) <= 140737488353712 -> aligned (V 35%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xa8e44 M) (st fx' R' 0xade6c M')
        /\ (forall x, In x KS_bhaG -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 689344
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 464)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 1024)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G1 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 K8 K9 pvzI9 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 pvzI10 K23.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV8l; move HV8l before pvzI2; pose proof (proj2 pvzI2) as HV8r; move HV8r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV58l; move HV58l before pvzI6; pose proof (proj2 pvzI6) as HV58r; move HV58r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K10l; move K10l before pvzI9; pose proof (proj2 pvzI9) as K10r; move K10r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K22l; move K22l before pvzI10; pose proof (proj2 pvzI10) as K22r; move K22r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_8 := V 8%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_58 := V 58%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 8%nat => Z_to_bv 64 vz_8 | 35%nat => Z_to_bv 64 vz_35 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 58%nat => Z_to_bv 64 vz_58 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 8%nat => vz_8 | 35%nat => vz_35 | 40%nat => vz_40 | 41%nat => vz_41 | 58%nat => vz_58 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PbhaG.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhaG.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhaG.kn0).
  { unfold know_ok, PbhaG.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear - HV35l HV35r K22l K22r) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear - HV8l HV8r) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K20]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r) | clear; lia | exact K23]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhaG.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhaG.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbhaG.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhaG.ps0) with 0xade6c in Hms. change (SR.ps_regs PbhaG.ps0) with (map (fun i => (i, nth i PbhaG.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhaG.ps0) with PbhaG.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhaG.regs0 PbhaG.regs_out0 64 KS_bhaG KS_bhaG_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhaG.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaG.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbhaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaG.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbhaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaG.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbhaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaG.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaG.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbhaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaG.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbhaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbhaG.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbhaG.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbhaH := LibSegBa_bhaH_b.
Definition KS_bhaH : list nat := Eval vm_compute in (BG.kept_list 64 PbhaH.regs0 PbhaH.regs_out0).
Lemma KS_bhaH_ok : BG.kept_ok 64 PbhaH.regs0 PbhaH.regs_out0 KS_bhaH = true. Proof. vm_compute. reflexivity. Qed.
Lemma bhaH_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 22) = Z_to_bv 64 ((V 40%nat) + 464) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 1024) -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 18446744073709551608 ->
  140735332487360 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 40%nat) <= 140737488353280 ->
  aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 2048 -> L5.writable RSEGS M (V 40%nat) 2048 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 2048 <= 2147446784) ->
  L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 256 -> L5.u64_at RSEGS M ((V 40%nat) + 2040) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 2048 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 128) + 144 <= (V 40%nat) \/ (V 40%nat) + 2048 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 144 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 128)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 8) -> ~ (((V 40%nat) + 464) <= bv_unsigned a < ((V 40%nat) + 464) + 8) -> ~ ((((V 40%nat) / 8) + 2147451008) <= bv_unsigned a < (((V 40%nat) / 8) + 2147451008) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 8) -> ~ (((V 40%nat) + 464) <= i < ((V 40%nat) + 464) + 8) -> ~ ((((V 40%nat) / 8) + 2147451008) <= i < (((V 40%nat) / 8) + 2147451008) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xa84c0 M) (st fx' R' 0xab620 M')
        /\ (forall x, In x KS_bhaH -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 689380
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) ((V 40%nat) + 856)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 464) 1251928
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451009) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147451008) 248
        /\ L5.defined M' (V 40%nat) 464
        /\ L5.defined M' ((V 40%nat) + 472) 1576).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G1 G2 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 pvzI5 K1 K2 pvzI6 K4 K5 K6 K7 K8 K9 pvzI7 K11 K12 K13 K14 K15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV41l; move HV41l before pvzI3; pose proof (proj2 pvzI3) as HV41r; move HV41r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV58l; move HV58l before pvzI4; pose proof (proj2 pvzI4) as HV58r; move HV58r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K10l; move K10l before pvzI7; pose proof (proj2 pvzI7) as K10r; move K10r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_58 := V 58%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 58%nat => Z_to_bv 64 vz_58 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 41%nat => vz_41 | 58%nat => vz_58 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PbhaH.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbhaH.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbhaH.kn0).
  { unfold know_ok, PbhaH.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | clear - HV40l HV40r K3l K3r K7 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | clear - HV41l HV41r K10l K10r K12 K13 K15; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbhaH.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbhaH.NX0 with 64%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 104) <= bv_unsigned a < (vz_2 - 104) + 8) -> ~ ((vz_40 + 464) <= bv_unsigned a < (vz_40 + 464) + 8) -> ~ (((vz_40 / 8) + 2147451008) <= bv_unsigned a < ((vz_40 / 8) + 2147451008) + 2) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbhaH.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K3l K3r K7 K13 K14 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbhaH.ps0) with 0xab620 in Hms. change (SR.ps_regs PbhaH.ps0) with (map (fun i => (i, nth i PbhaH.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbhaH.ps0) with PbhaH.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbhaH.regs0 PbhaH.regs_out0 64 KS_bhaH KS_bhaH_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbhaH.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbhaH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbhaH.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbhaH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

End PNAHP2.
