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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_azcS0_b LibSegBa_azcS1_b LibSegBa_azcS2_b LibSegBa_azcS3_b LibSegBa_azcS4_b LibSegBa_azcS5_b LibSegBa_azcS6_b LibSegBa_azcS7_b LibSegBa_azcS8_b LibSegBa_azcS9_b LibSegBa_azcS10_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAECP2.
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
Module PazcS0 := LibSegBa_azcS0_b.
Definition KS_azcS0 : list nat := Eval vm_compute in (BG.kept_list 60 PazcS0.regs0 PazcS0.regs_out0).
Lemma KS_azcS0_ok : BG.kept_ok 60 PazcS0.regs0 PazcS0.regs_out0 KS_azcS0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcS0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 40) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 40) ->
  4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2758 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_azcS0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710136
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 9) = Z_to_bv 64 2
        /\ getr R' (reg 10) = Z_to_bv 64 80
        /\ getr R' (reg 11) = Z_to_bv 64 2
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 19) = Z_to_bv 64 1
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731192
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 G13 pvzI7 K1 K2 K3 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13 K14 K15 pvzI9 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV52l; move HV52l before pvzI6; pose proof (proj2 pvzI6) as HV52r; move HV52r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcS0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcS0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcS0.kn0).
  { unfold know_ok, PazcS0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcS0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcS0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 192) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PazcS0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcS0.ps0) with 0x130338 in Hms. change (SR.ps_regs PazcS0.ps0) with (map (fun i => (i, nth i PazcS0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcS0.ps0) with PazcS0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcS0.regs0 PazcS0.regs_out0 60 KS_azcS0 KS_azcS0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcS0.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcS1 := LibSegBa_azcS1_b.
Definition KS_azcS1 : list nat := Eval vm_compute in (BG.kept_list 60 PazcS1.regs0 PazcS1.regs_out0).
Lemma KS_azcS1_ok : BG.kept_ok 60 PazcS1.regs0 PazcS1.regs_out0 KS_azcS1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcS1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 80) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 80) ->
  4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2758 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_azcS1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710136
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 9) = Z_to_bv 64 4
        /\ getr R' (reg 10) = Z_to_bv 64 160
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 19) = Z_to_bv 64 2
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731192
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 G13 pvzI7 K1 K2 K3 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13 K14 K15 pvzI9 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV52l; move HV52l before pvzI6; pose proof (proj2 pvzI6) as HV52r; move HV52r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcS1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcS1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcS1.kn0).
  { unfold know_ok, PazcS1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcS1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcS1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 192) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PazcS1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcS1.ps0) with 0x130338 in Hms. change (SR.ps_regs PazcS1.ps0) with (map (fun i => (i, nth i PazcS1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcS1.ps0) with PazcS1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcS1.regs0 PazcS1.regs_out0 60 KS_azcS1 KS_azcS1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcS1.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcS2 := LibSegBa_azcS2_b.
Definition KS_azcS2 : list nat := Eval vm_compute in (BG.kept_list 60 PazcS2.regs0 PazcS2.regs_out0).
Lemma KS_azcS2_ok : BG.kept_ok 60 PazcS2.regs0 PazcS2.regs_out0 KS_azcS2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcS2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 160) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 160) ->
  4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2758 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_azcS2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710136
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 9) = Z_to_bv 64 8
        /\ getr R' (reg 10) = Z_to_bv 64 320
        /\ getr R' (reg 11) = Z_to_bv 64 8
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 19) = Z_to_bv 64 4
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731192
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 G13 pvzI7 K1 K2 K3 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13 K14 K15 pvzI9 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV52l; move HV52l before pvzI6; pose proof (proj2 pvzI6) as HV52r; move HV52r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcS2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcS2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcS2.kn0).
  { unfold know_ok, PazcS2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcS2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcS2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 192) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PazcS2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcS2.ps0) with 0x130338 in Hms. change (SR.ps_regs PazcS2.ps0) with (map (fun i => (i, nth i PazcS2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcS2.ps0) with PazcS2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcS2.regs0 PazcS2.regs_out0 60 KS_azcS2 KS_azcS2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcS2.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcS3 := LibSegBa_azcS3_b.
Definition KS_azcS3 : list nat := Eval vm_compute in (BG.kept_list 60 PazcS3.regs0 PazcS3.regs_out0).
Lemma KS_azcS3_ok : BG.kept_ok 60 PazcS3.regs0 PazcS3.regs_out0 KS_azcS3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcS3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 320) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 320) ->
  4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2758 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_azcS3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710136
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 9) = Z_to_bv 64 16
        /\ getr R' (reg 10) = Z_to_bv 64 640
        /\ getr R' (reg 11) = Z_to_bv 64 16
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 19) = Z_to_bv 64 8
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731192
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 G13 pvzI7 K1 K2 K3 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13 K14 K15 pvzI9 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV52l; move HV52l before pvzI6; pose proof (proj2 pvzI6) as HV52r; move HV52r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcS3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcS3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcS3.kn0).
  { unfold know_ok, PazcS3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcS3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcS3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 192) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PazcS3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcS3.ps0) with 0x130338 in Hms. change (SR.ps_regs PazcS3.ps0) with (map (fun i => (i, nth i PazcS3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcS3.ps0) with PazcS3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcS3.regs0 PazcS3.regs_out0 60 KS_azcS3 KS_azcS3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS3.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcS3.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcS4 := LibSegBa_azcS4_b.
Definition KS_azcS4 : list nat := Eval vm_compute in (BG.kept_list 60 PazcS4.regs0 PazcS4.regs_out0).
Lemma KS_azcS4_ok : BG.kept_ok 60 PazcS4.regs0 PazcS4.regs_out0 KS_azcS4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcS4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 640) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 640) ->
  4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2758 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_azcS4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710136
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 9) = Z_to_bv 64 32
        /\ getr R' (reg 10) = Z_to_bv 64 1280
        /\ getr R' (reg 11) = Z_to_bv 64 32
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 19) = Z_to_bv 64 16
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731192
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 G13 pvzI7 K1 K2 K3 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13 K14 K15 pvzI9 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV52l; move HV52l before pvzI6; pose proof (proj2 pvzI6) as HV52r; move HV52r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcS4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcS4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcS4.kn0).
  { unfold know_ok, PazcS4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcS4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcS4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 192) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PazcS4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcS4.ps0) with 0x130338 in Hms. change (SR.ps_regs PazcS4.ps0) with (map (fun i => (i, nth i PazcS4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcS4.ps0) with PazcS4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcS4.regs0 PazcS4.regs_out0 60 KS_azcS4 KS_azcS4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS4.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcS4.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcS5 := LibSegBa_azcS5_b.
Definition KS_azcS5 : list nat := Eval vm_compute in (BG.kept_list 60 PazcS5.regs0 PazcS5.regs_out0).
Lemma KS_azcS5_ok : BG.kept_ok 60 PazcS5.regs0 PazcS5.regs_out0 KS_azcS5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcS5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 1280) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 1280) ->
  4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2758 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_azcS5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710136
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 9) = Z_to_bv 64 64
        /\ getr R' (reg 10) = Z_to_bv 64 2560
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 19) = Z_to_bv 64 32
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731192
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 G13 pvzI7 K1 K2 K3 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13 K14 K15 pvzI9 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV52l; move HV52l before pvzI6; pose proof (proj2 pvzI6) as HV52r; move HV52r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcS5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcS5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcS5.kn0).
  { unfold know_ok, PazcS5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcS5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcS5.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 192) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PazcS5.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcS5.ps0) with 0x130338 in Hms. change (SR.ps_regs PazcS5.ps0) with (map (fun i => (i, nth i PazcS5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcS5.ps0) with PazcS5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcS5.regs0 PazcS5.regs_out0 60 KS_azcS5 KS_azcS5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS5.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcS5.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcS6 := LibSegBa_azcS6_b.
Definition KS_azcS6 : list nat := Eval vm_compute in (BG.kept_list 60 PazcS6.regs0 PazcS6.regs_out0).
Lemma KS_azcS6_ok : BG.kept_ok 60 PazcS6.regs0 PazcS6.regs_out0 KS_azcS6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcS6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 2560) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 2560) ->
  4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2758 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_azcS6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710136
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 9) = Z_to_bv 64 128
        /\ getr R' (reg 10) = Z_to_bv 64 5120
        /\ getr R' (reg 11) = Z_to_bv 64 128
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 19) = Z_to_bv 64 64
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731192
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 G13 pvzI7 K1 K2 K3 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13 K14 K15 pvzI9 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV52l; move HV52l before pvzI6; pose proof (proj2 pvzI6) as HV52r; move HV52r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcS6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcS6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcS6.kn0).
  { unfold know_ok, PazcS6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcS6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcS6.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 192) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PazcS6.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcS6.ps0) with 0x130338 in Hms. change (SR.ps_regs PazcS6.ps0) with (map (fun i => (i, nth i PazcS6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcS6.ps0) with PazcS6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcS6.regs0 PazcS6.regs_out0 60 KS_azcS6 KS_azcS6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS6.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcS6.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcS7 := LibSegBa_azcS7_b.
Definition KS_azcS7 : list nat := Eval vm_compute in (BG.kept_list 60 PazcS7.regs0 PazcS7.regs_out0).
Lemma KS_azcS7_ok : BG.kept_ok 60 PazcS7.regs0 PazcS7.regs_out0 KS_azcS7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcS7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 5120) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 5120) ->
  4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2758 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_azcS7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710136
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 9) = Z_to_bv 64 256
        /\ getr R' (reg 10) = Z_to_bv 64 10240
        /\ getr R' (reg 11) = Z_to_bv 64 256
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 19) = Z_to_bv 64 128
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731192
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 G13 pvzI7 K1 K2 K3 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13 K14 K15 pvzI9 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV52l; move HV52l before pvzI6; pose proof (proj2 pvzI6) as HV52r; move HV52r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcS7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcS7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcS7.kn0).
  { unfold know_ok, PazcS7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcS7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcS7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 192) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PazcS7.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcS7.ps0) with 0x130338 in Hms. change (SR.ps_regs PazcS7.ps0) with (map (fun i => (i, nth i PazcS7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcS7.ps0) with PazcS7.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcS7.regs0 PazcS7.regs_out0 60 KS_azcS7 KS_azcS7_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS7.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcS7.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcS8 := LibSegBa_azcS8_b.
Definition KS_azcS8 : list nat := Eval vm_compute in (BG.kept_list 60 PazcS8.regs0 PazcS8.regs_out0).
Lemma KS_azcS8_ok : BG.kept_ok 60 PazcS8.regs0 PazcS8.regs_out0 KS_azcS8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcS8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 10240) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 10240) ->
  4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2758 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_azcS8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710136
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 9) = Z_to_bv 64 512
        /\ getr R' (reg 10) = Z_to_bv 64 20480
        /\ getr R' (reg 11) = Z_to_bv 64 512
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 19) = Z_to_bv 64 256
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731192
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 G13 pvzI7 K1 K2 K3 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13 K14 K15 pvzI9 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV52l; move HV52l before pvzI6; pose proof (proj2 pvzI6) as HV52r; move HV52r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcS8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcS8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcS8.kn0).
  { unfold know_ok, PazcS8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcS8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcS8.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 192) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PazcS8.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcS8.ps0) with 0x130338 in Hms. change (SR.ps_regs PazcS8.ps0) with (map (fun i => (i, nth i PazcS8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcS8.ps0) with PazcS8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcS8.regs0 PazcS8.regs_out0 60 KS_azcS8 KS_azcS8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS8.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcS8.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcS9 := LibSegBa_azcS9_b.
Definition KS_azcS9 : list nat := Eval vm_compute in (BG.kept_list 60 PazcS9.regs0 PazcS9.regs_out0).
Lemma KS_azcS9_ok : BG.kept_ok 60 PazcS9.regs0 PazcS9.regs_out0 KS_azcS9 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcS9_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 20480) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 20480) ->
  4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2758 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_azcS9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710136
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 9) = Z_to_bv 64 1024
        /\ getr R' (reg 10) = Z_to_bv 64 40960
        /\ getr R' (reg 11) = Z_to_bv 64 1024
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 19) = Z_to_bv 64 512
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731192
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 G13 pvzI7 K1 K2 K3 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13 K14 K15 pvzI9 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV52l; move HV52l before pvzI6; pose proof (proj2 pvzI6) as HV52r; move HV52r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcS9.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcS9.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcS9.kn0).
  { unfold know_ok, PazcS9.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcS9.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcS9.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 192) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PazcS9.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcS9.ps0) with 0x130338 in Hms. change (SR.ps_regs PazcS9.ps0) with (map (fun i => (i, nth i PazcS9.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcS9.ps0) with PazcS9.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcS9.regs0 PazcS9.regs_out0 60 KS_azcS9 KS_azcS9_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS9.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcS9.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcS10 := LibSegBa_azcS10_b.
Definition KS_azcS10 : list nat := Eval vm_compute in (BG.kept_list 60 PazcS10.regs0 PazcS10.regs_out0).
Lemma KS_azcS10_ok : BG.kept_ok 60 PazcS10.regs0 PazcS10.regs_out0 KS_azcS10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcS10_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 40960) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 40960) ->
  4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2758 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_azcS10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710136
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 9) = Z_to_bv 64 2048
        /\ getr R' (reg 10) = Z_to_bv 64 81920
        /\ getr R' (reg 11) = Z_to_bv 64 2048
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 19) = Z_to_bv 64 1024
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731192
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 G12 G13 pvzI7 K1 K2 K3 K4 K5 K6 pvzI8 K8 K9 K10 K11 K12 K13 K14 K15 pvzI9 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV52l; move HV52l before pvzI6; pose proof (proj2 pvzI6) as HV52r; move HV52r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K7l; move K7l before pvzI8; pose proof (proj2 pvzI8) as K7r; move K7r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K16l; move K16l before pvzI9; pose proof (proj2 pvzI9) as K16r; move K16r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcS10.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcS10.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcS10.kn0).
  { unfold know_ok, PazcS10.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcS10.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcS10.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 192) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PazcS10.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcS10.ps0) with 0x130338 in Hms. change (SR.ps_regs PazcS10.ps0) with (map (fun i => (i, nth i PazcS10.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcS10.ps0) with PazcS10.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcS10.regs0 PazcS10.regs_out0 60 KS_azcS10 KS_azcS10_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcS10.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcS10.regs_out0]. rewrite (BG.edenot_kept 60 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia].
Qed.
(* [comment removed for export] *)

End PNAECP2.
