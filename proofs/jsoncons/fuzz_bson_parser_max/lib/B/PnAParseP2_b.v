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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_apaD5a_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAPAP2.
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
Module PapaD5a := LibSegBa_apaD5a_b.
Definition KS_apaD5a : list nat := Eval vm_compute in (BG.kept_list 80 PapaD5a.regs0 PapaD5a.regs_out0).
Lemma KS_apaD5a_ok : BG.kept_ok 80 PapaD5a.regs0 PapaD5a.regs_out0 KS_apaD5a = true. Proof. vm_compute. reflexivity. Qed.
Lemma apaD5a_conc fx R M (V : nat -> Z) :
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
        /\ (forall x, In x KS_apaD5a -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 11) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 33%nat) + 8)
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
  assert (HR: regs_ok E PapaD5a.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PapaD5a.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PapaD5a.kn0).
  { unfold know_ok, PapaD5a.kn0.
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
  pvz_hg ltac:(idtac; destruct (PapaD5a.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PapaD5a.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_42 - 40) <= bv_unsigned a < (vz_42 - 40) + 4) -> ~ ((vz_42 - 16) <= bv_unsigned a < (vz_42 - 16) + 1) -> ~ ((((vz_50 / 8) + 2147450880) + 4) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 4) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PapaD5a.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk' ZA Hag ltac:(clear) | clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K48 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PapaD5a.ps0) with 0xae3fc in Hms. change (SR.ps_regs PapaD5a.ps0) with (map (fun i => (i, nth i PapaD5a.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PapaD5a.ps0) with PapaD5a.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PapaD5a.regs0 PapaD5a.regs_out0 80 KS_apaD5a KS_apaD5a_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PapaD5a.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PapaD5a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD5a.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PapaD5a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD5a.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PapaD5a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD5a.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PapaD5a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PapaD5a.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PapaD5a.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk' ZA Hag ltac:(clear - HV45l HV45r K58l K58r) | byte_tac ltac:(clear - HV45l HV45r K58l K58r) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV42l HV42r K42l K42r K43 K45 K46 K47 K48 K49) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

End PNAPAP2.
