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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_awvX0S_b LibSegBa_awvX0L_b LibSegBa_awvX1_b LibSegBa_awvX2_b LibSegBa_awvX3_b LibSegBa_awvX4_b LibSegBa_awvXR_b LibSegBa_awvX5S_b LibSegBa_awvX5L_b LibSegBa_awvX6_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARVXP.
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
Module PawvX0S := LibSegBa_awvX0S_b.
Definition KS_awvX0S : list nat := Eval vm_compute in (BG.kept_list 80 PawvX0S.regs0 PawvX0S.regs_out0).
Lemma KS_awvX0S_ok : BG.kept_ok 80 PawvX0S.regs0 PawvX0S.regs_out0 KS_awvX0S = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvX0S_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 368) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 369) / 8) + 2147450880) 1 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) ->
  ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) ->
  (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) -> L5.u8_at RSEGS M ((V 33%nat) + 368) (V 56%nat) -> 0 <= (V 56%nat) <= 255 ->
  Z.testbit (V 56%nat) 0 = false -> L5.writable RSEGS M ((V 33%nat) + 368) 2 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 368) <= bv_unsigned a < ((V 33%nat) + 368) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 368) <= i < ((V 33%nat) + 368) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0610 M) (st fx' R' 0xd5bc4 M')
        /\ (forall x, In x KS_awvX0S -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 724992
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 368)
        /\ getr R' (reg 11) = Z_to_bv 64 47
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 368)
        /\ getr R' (reg 24) = Z_to_bv 64 ((((V 33%nat) + 368) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 368) 0
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 369) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G18 G19 G20 G21 G22 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 K14 pvzI10 K16 K17 K18 K19 K20 K21 pvzI11 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 pvzI12 K36 K37.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K15l; move K15l before pvzI10; pose proof (proj2 pvzI10) as K15r; move K15r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K22l; move K22l before pvzI11; pose proof (proj2 pvzI11) as K22r; move K22r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K35l; move K35l before pvzI12; pose proof (proj2 pvzI12) as K35r; move K35r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_56 := V 56%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 56%nat => Z_to_bv 64 vz_56 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 56%nat => vz_56 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PawvX0S.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvX0S.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvX0S.kn0).
  { unfold know_ok, PawvX0S.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K26 K27) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K26 K27) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K26 K27) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K14 K26 K27; lia | clear - HV2l HV2r K3l K3r K14 K26 K27; lia | clear - HV2l HV2r K3l K3r K14 K26 K27; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | exactA K12]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32; lia | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32; lia | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32; lia | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32; lia | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32; lia | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32; lia | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32) | evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33) | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32; lia | clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33; lia | clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33; lia | clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K14 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K15l K15r K19 K25 K26 K28 K30 K31 K32) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K22l K22r K24 K25 K27 K29 K33) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | evalEk ZA ltac:(clear - HV56l HV56r K35l K35r K36) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | byte_tac ltac:(clear - HV56l HV56r K35l K35r K36) | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K35l K35r K36) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV56l HV56r K35l K35r K36) | clear; lia | rewrite (L5K.land1_bit0_false vz_56 ltac:(clear - HV56l HV56r K35l K35r K36; lia) K36); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30; lia | exactA K37]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvX0S.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvX0S.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 368) <= bv_unsigned a < (vz_33 + 368) + 2) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PawvX0S.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvX0S.ps0) with 0xd5bc4 in Hms. change (SR.ps_regs PawvX0S.ps0) with (map (fun i => (i, nth i PawvX0S.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvX0S.ps0) with PawvX0S.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvX0S.regs0 PawvX0S.regs_out0 80 KS_awvX0S KS_awvX0S_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvX0S.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvX0S.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX0S.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvX0S.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX0S.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvX0S.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX0S.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PawvX0S.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX0S.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PawvX0S.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K14 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvX0L := LibSegBa_awvX0L_b.
Definition KS_awvX0L : list nat := Eval vm_compute in (BG.kept_list 80 PawvX0L.regs0 PawvX0L.regs_out0).
Lemma KS_awvX0L_ok : BG.kept_ok 80 PawvX0L.regs0 PawvX0L.regs_out0 KS_awvX0L = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvX0L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 368) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 384) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 376) / 8) + 2147450880) 1 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) -> L5.u8_at RSEGS M ((V 33%nat) + 368) (V 56%nat) ->
  0 <= (V 56%nat) <= 255 -> Z.testbit (V 56%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 384) (V 57%nat) -> 4096 <= (V 57%nat) <= 140737488355320 ->
  aligned (V 57%nat) 8 -> L5.u64_at RSEGS M ((V 33%nat) + 376) (V 58%nat) -> (2147446784 + 17592186048512 <= (V 57%nat) \/ (V 57%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 57%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 57%nat) 1 -> (((V 2%nat) - 160) + 160 <= (V 57%nat) \/ (V 57%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 57%nat) + 1 <= (V 33%nat) \/ (V 33%nat) + 416 <= (V 57%nat)) -> (65536 + 6840320 <= (V 57%nat) \/ (V 57%nat) + 1 <= 65536) ->
  L5.writable RSEGS M ((V 33%nat) + 376) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 57%nat) + 0) <= bv_unsigned a < ((V 57%nat) + 0) + 1) -> ~ (((V 33%nat) + 376) <= bv_unsigned a < ((V 33%nat) + 376) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 57%nat) + 0) <= i < ((V 57%nat) + 0) + 1) -> ~ (((V 33%nat) + 376) <= i < ((V 33%nat) + 376) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0610 M) (st fx' R' 0xd5bc4 M')
        /\ (forall x, In x KS_awvX0L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 724992
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 368)
        /\ getr R' (reg 11) = Z_to_bv 64 47
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 368)
        /\ getr R' (reg 24) = Z_to_bv 64 ((((V 33%nat) + 368) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 376) 0
        /\ L5.u8_at RSEGS M' (V 57%nat) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G18 G19 G20 G21 G22 G26 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 K13 K14 K15 pvzI12 K17 K18 K19 K20 K21 K22 pvzI13 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 pvzI14 K37 K38 pvzI15 K40 K41 K42 K43 K44 K45 K46 K47 K48.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV58l; move HV58l before pvzI9; pose proof (proj2 pvzI9) as HV58r; move HV58r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K16l; move K16l before pvzI12; pose proof (proj2 pvzI12) as K16r; move K16r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K23l; move K23l before pvzI13; pose proof (proj2 pvzI13) as K23r; move K23r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K36l; move K36l before pvzI14; pose proof (proj2 pvzI14) as K36r; move K36r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K39l; move K39l before pvzI15; pose proof (proj2 pvzI15) as K39r; move K39r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PawvX0L.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvX0L.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvX0L.kn0).
  { unfold know_ok, PawvX0L.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K45) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K45) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K45) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K15 K27 K28 K45; lia | clear - HV2l HV2r K3l K3r K15 K27 K28 K45; lia | clear - HV2l HV2r K3l K3r K15 K27 K28 K45; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | exactA K12]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | exactA K13]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34; lia | clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34; lia | clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear - HV56l HV56r K36l K36r K37) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | byte_tac ltac:(clear - HV56l HV56r K36l K36r K37) | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K36l K36r K37) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV56l HV56r K36l K36r K37) | clear; lia | rewrite (L5K.land1_bit0_true vz_56 ltac:(clear - HV56l HV56r K36l K36r K37; lia) K37); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear - HV57l HV57r K39l K39r K42 K45 K46 K47) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K39l K39r K42 K45 K46 K47) | exact (conj K39l K39r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV57l HV57r K39l K39r K42 K45 K46 K47) | clear; lia | exact K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K39l K39r K42 K45 K46 K47) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV57l HV57r K39l K39r K42 K45 K46 K47) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K39l K39r K42 K45 K46 K47; lia | clear - HV57l HV57r K39l K39r K42 K45 K46 K47; lia | clear - HV57l HV57r K39l K39r K42 K45 K46 K47; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV57l HV57r K39l K39r K42 K45 K46 K47) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K39l K39r K42 K45 K46 K47; lia | clear - HV57l HV57r K39l K39r K42 K45 K46 K47; lia | clear - HV57l HV57r K39l K39r K42 K45 K46 K47; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K39l K39r K42 K45 K46 K47) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV57l HV57r K39l K39r K42 K45 K46 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K39l K39r K42 K45 K46 K47) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46; lia | exactA K48]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvX0L.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvX0L.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_57 + 0) <= bv_unsigned a < (vz_57 + 0) + 1) -> ~ ((vz_33 + 376) <= bv_unsigned a < (vz_33 + 376) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PawvX0L.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV57l HV57r K39l K39r K42 K45 K46 K47) | evalEk' ZA Hag ltac:(clear) | clear - HV57l HV57r K39l K39r K42 K45 K46 K47 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvX0L.ps0) with 0xd5bc4 in Hms. change (SR.ps_regs PawvX0L.ps0) with (map (fun i => (i, nth i PawvX0L.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvX0L.ps0) with PawvX0L.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvX0L.regs0 PawvX0L.regs_out0 80 KS_awvX0L KS_awvX0L_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvX0L.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvX0L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX0L.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvX0L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX0L.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvX0L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX0L.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PawvX0L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX0L.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PawvX0L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K46) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV57l HV57r K39l K39r K42 K45 K46 K47) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvX1 := LibSegBa_awvX1_b.
Definition KS_awvX1 : list nat := Eval vm_compute in (BG.kept_list 80 PawvX1.regs0 PawvX1.regs_out0).
Lemma KS_awvX1_ok : BG.kept_ok 80 PawvX1.regs0 PawvX1.regs_out0 KS_awvX1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvX1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 368) -> getr R (reg 24) = Z_to_bv 64 ((((V 33%nat) + 368) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487392 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1000 M) (st fx' R' 0xb2cd0 M')
        /\ (forall x, In x KS_awvX1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 725008
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 368)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G26 G27 pvzI6 K1 K2 pvzI7 K4.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvX1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvX1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvX1.kn0).
  { unfold know_ok, PawvX1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvX1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvX1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvX1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvX1.ps0) with 0xb2cd0 in Hms. change (SR.ps_regs PawvX1.ps0) with (map (fun i => (i, nth i PawvX1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvX1.ps0) with PawvX1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvX1.regs0 PawvX1.regs_out0 80 KS_awvX1 KS_awvX1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvX1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvX1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvX1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvX2 := LibSegBa_awvX2_b.
Definition KS_awvX2_0 : list nat := Eval vm_compute in (BG.kept_list 80 PawvX2.regs0 PawvX2.regs_out0).
Lemma KS_awvX2_0_ok : BG.kept_ok 80 PawvX2.regs0 PawvX2.regs_out0 KS_awvX2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_awvX2_1 : list nat := Eval vm_compute in (BG.kept_list 80 PawvX2.regs0 PawvX2.regs_out1).
Lemma KS_awvX2_1_ok : BG.kept_ok 80 PawvX2.regs0 PawvX2.regs_out1 KS_awvX2_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvX2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 368) -> getr R (reg 24) = Z_to_bv 64 ((((V 33%nat) + 368) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  6905856 <= (V 36%nat) <= 140737488355312 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 2 ->
  (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 16 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 36%nat) \/ (V 36%nat) + 16 <= (V 33%nat)) -> ((V 50%nat) + 512 <= (V 36%nat) \/ (V 36%nat) + 16 <= (V 50%nat)) -> ((V 51%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 16 <= (V 51%nat)) ->
  L5.u32_at RSEGS M (V 36%nat) (V 44%nat) -> 0 <= (V 44%nat) <= 64 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb1010 M) (st fx' R' 0xd5bc4 M')
        /\ (forall x, In x KS_awvX2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 725044
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 368)
        /\ getr R' (reg 11) = Z_to_bv 64 47
        /\ getr R' (reg 25) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880)
        /\ (((V 44%nat) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb1010 M) (st fx' R' 0xb1424 M')
        /\ (forall x, In x KS_awvX2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880)
        /\ 1 <= (((V 44%nat) - 0) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 pvzI10 K14 K15 K16 K17 K18 K19 pvzI11 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 pvzI12 K33 K34 K35 K36 K37 K38 K39 K40 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K13l; move K13l before pvzI10; pose proof (proj2 pvzI10) as K13r; move K13r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K20l; move K20l before pvzI11; pose proof (proj2 pvzI11) as K20r; move K20r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K32l; move K32l before pvzI12; pose proof (proj2 pvzI12) as K32r; move K32r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K41l; move K41l before pvzI13; pose proof (proj2 pvzI13) as K41r; move K41r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 44%nat => Z_to_bv 64 vz_44 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 44%nat => vz_44 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvX2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvX2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvX2.kn0).
  { unfold know_ok, PawvX2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39; lia | clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39; lia | clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear - HV44l HV44r K41l K41r) | clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39; lia | clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvX2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvX2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvX2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PawvX2.ps0) with 0xd5bc4 in Hms. change (SR.ps_regs PawvX2.ps0) with (map (fun i => (i, nth i PawvX2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PawvX2.ps0) with PawvX2.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvX2.regs0 PawvX2.regs_out0 80 KS_awvX2_0 KS_awvX2_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PawvX2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvX2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvX2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvX2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvX2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvX2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvX2.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PawvX2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PawvX2.ps1) with 0xb1424 in Hms. change (SR.ps_regs PawvX2.ps1) with (map (fun i => (i, nth i PawvX2.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PawvX2.ps1) with PawvX2.cells1 in Hcells. unfold PawvX2.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvX2.regs0 PawvX2.regs_out1 80 KS_awvX2_1 KS_awvX2_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PawvX2.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvX2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PawvX2.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PawvX2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvX3 := LibSegBa_awvX3_b.
Definition KS_awvX3 : list nat := Eval vm_compute in (BG.kept_list 80 PawvX3.regs0 PawvX3.regs_out0).
Lemma KS_awvX3_ok : BG.kept_ok 80 PawvX3.regs0 PawvX3.regs_out0 KS_awvX3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvX3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 368) -> getr R (reg 24) = Z_to_bv 64 ((((V 33%nat) + 368) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487392 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> 6905856 <= (V 36%nat) <= 140737488355312 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1034 M) (st fx' R' 0xb2cd0 M')
        /\ (forall x, In x KS_awvX3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 725060
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 33%nat) + 368)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI6 K1 K2 pvzI7 K4 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K5l; move K5l before pvzI8; pose proof (proj2 pvzI8) as K5r; move K5r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvX3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvX3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvX3.kn0).
  { unfold know_ok, PawvX3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvX3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvX3.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvX3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvX3.ps0) with 0xb2cd0 in Hms. change (SR.ps_regs PawvX3.ps0) with (map (fun i => (i, nth i PawvX3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvX3.ps0) with PawvX3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvX3.regs0 PawvX3.regs_out0 80 KS_awvX3 KS_awvX3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvX3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvX3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvX3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvX3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvX3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvX3.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvX4 := LibSegBa_awvX4_b.
Definition KS_awvX4_0 : list nat := Eval vm_compute in (BG.kept_list 80 PawvX4.regs0 PawvX4.regs_out0).
Lemma KS_awvX4_0_ok : BG.kept_ok 80 PawvX4.regs0 PawvX4.regs_out0 KS_awvX4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_awvX4_1 : list nat := Eval vm_compute in (BG.kept_list 80 PawvX4.regs0 PawvX4.regs_out1).
Lemma KS_awvX4_1_ok : BG.kept_ok 80 PawvX4.regs0 PawvX4.regs_out1 KS_awvX4_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvX4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 368) -> getr R (reg 24) = Z_to_bv 64 ((((V 33%nat) + 368) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  6905856 <= (V 36%nat) <= 140737488355312 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 2 ->
  (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 16 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 36%nat) \/ (V 36%nat) + 16 <= (V 33%nat)) -> ((V 50%nat) + 512 <= (V 36%nat) \/ (V 36%nat) + 16 <= (V 50%nat)) -> ((V 51%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 16 <= (V 51%nat)) ->
  L5.u32_at RSEGS M (V 36%nat) (V 44%nat) -> 0 <= (V 44%nat) <= 64 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb1044 M) (st fx' R' 0xb1054 M')
        /\ (forall x, In x KS_awvX4_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 44%nat)
        /\ (((V 44%nat) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb1044 M) (st fx' R' 0xb1424 M')
        /\ (forall x, In x KS_awvX4_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 44%nat)
        /\ 1 <= (((V 44%nat) - 0) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 pvzI10 K14 K15 K16 K17 K18 K19 pvzI11 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 pvzI12 K33 K34 K35 K36 K37 K38 K39 K40 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K13l; move K13l before pvzI10; pose proof (proj2 pvzI10) as K13r; move K13r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K20l; move K20l before pvzI11; pose proof (proj2 pvzI11) as K20r; move K20r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K32l; move K32l before pvzI12; pose proof (proj2 pvzI12) as K32r; move K32r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K41l; move K41l before pvzI13; pose proof (proj2 pvzI13) as K41r; move K41r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 44%nat => Z_to_bv 64 vz_44 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 44%nat => vz_44 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvX4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvX4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvX4.kn0).
  { unfold know_ok, PawvX4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | clear - HV2l HV2r K3l K3r K12 K24 K25 K36; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39; lia | clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39; lia | clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear - HV44l HV44r K41l K41r) | clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39; lia | clear - HV36l HV36r K32l K32r K34 K36 K37 K38 K39; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvX4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvX4.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvX4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PawvX4.ps0) with 0xb1054 in Hms. change (SR.ps_regs PawvX4.ps0) with (map (fun i => (i, nth i PawvX4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PawvX4.ps0) with PawvX4.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvX4.regs0 PawvX4.regs_out0 80 KS_awvX4_0 KS_awvX4_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PawvX4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvX4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PawvX4.ps1) with 0xb1424 in Hms. change (SR.ps_regs PawvX4.ps1) with (map (fun i => (i, nth i PawvX4.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PawvX4.ps1) with PawvX4.cells1 in Hcells. unfold PawvX4.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvX4.regs0 PawvX4.regs_out1 80 KS_awvX4_1 KS_awvX4_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PawvX4.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvX4.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvXR := LibSegBa_awvXR_b.
Definition KS_awvXR : list nat := Eval vm_compute in (BG.kept_list 80 PawvXR.regs0 PawvXR.regs_out0).
Lemma KS_awvXR_ok : BG.kept_ok 80 PawvXR.regs0 PawvXR.regs_out0 KS_awvXR = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvXR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487392 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1424 M) (st fx' R' 0x7b90c M')
        /\ (forall x, In x KS_awvXR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726080
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.defined M' ((V 50%nat) + 8) 504).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G26 G27 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 K8 K9 pvzI9 K11 K12 K13 K14 K15 K16 K17 K18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K10l; move K10l before pvzI9; pose proof (proj2 pvzI9) as K10r; move K10r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvXR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvXR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvXR.kn0).
  { unfold know_ok, PawvXR.kn0.
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
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvXR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvXR.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PawvXR.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvXR.ps0) with 0x7b90c in Hms. change (SR.ps_regs PawvXR.ps0) with (map (fun i => (i, nth i PawvXR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvXR.ps0) with PawvXR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvXR.regs0 PawvXR.regs_out0 80 KS_awvXR KS_awvXR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvXR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvXR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvXR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvXR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvXR.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvXR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvX5S := LibSegBa_awvX5S_b.
Definition KS_awvX5S : list nat := Eval vm_compute in (BG.kept_list 80 PawvX5S.regs0 PawvX5S.regs_out0).
Lemma KS_awvX5S_ok : BG.kept_ok 80 PawvX5S.regs0 PawvX5S.regs_out0 KS_awvX5S = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma awvX5S_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 368) -> getr R (reg 24) = Z_to_bv 64 ((((V 33%nat) + 368) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 368) / 8) + 2147450880) 1 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) ->
  (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) -> 6905856 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 8 <= 2147446784) ->
  L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 160) + 160 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> ((V 50%nat) + 512 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 50%nat)) ->
  ((V 51%nat) + 1 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 51%nat)) -> L5.u64_at RSEGS M (V 34%nat) 1251456 -> L5KA.zeros_at M 2147607327 1 -> ((((V 34%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 34%nat) / 8) + 2147450880)) ->
  L5.u8_at RSEGS M ((V 33%nat) + 368) (V 56%nat) -> 0 <= (V 56%nat) <= 255 -> Z.testbit (V 56%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 20) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 20) + 2) -> ~ (((V 50%nat) + 160) <= bv_unsigned a < ((V 50%nat) + 160) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 20) <= i < ((((V 50%nat) / 8) + 2147450880) + 20) + 2) -> ~ (((V 50%nat) + 160) <= i < ((V 50%nat) + 160) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1054 M) (st fx' R' 0xb13d8 M')
        /\ (forall x, In x KS_awvX5S -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 725976
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 160)
        /\ getr R' (reg 12) = Z_to_bv 64 20
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 692916
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 168) ((V 56%nat) / 2)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 160) ((V 33%nat) + 369)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450901) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450900) 0
        /\ L5.defined M' (V 50%nat) 160
        /\ L5.defined M' ((V 50%nat) + 176) 336).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 K20 pvzI11 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI12 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 pvzI13 K46.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K21l; move K21l before pvzI11; pose proof (proj2 pvzI11) as K21r; move K21r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K33l; move K33l before pvzI12; pose proof (proj2 pvzI12) as K33r; move K33r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K45l; move K45l before pvzI13; pose proof (proj2 pvzI13) as K45r; move K45r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_56 := V 56%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 56%nat => Z_to_bv 64 vz_56 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 56%nat => vz_56 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PawvX5S.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvX5S.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvX5S.kn0).
  { unfold know_ok, PawvX5S.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K37) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K37) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K37) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K37; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K37; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K37; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K32 K40) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K32 K40) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K32 K40) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K32 K40; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K32 K40; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K32 K40; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K32 K40) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K32 K40) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K32 K40) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K32 K40) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K32 K40) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K33l K33r K35 K37 K38 K39 K40 K43) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K33l K33r K35 K37 K38 K39 K40 K43) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K33l K33r K35 K37 K38 K39 K40 K43) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K33l K33r K35 K37 K38 K39 K40 K43) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K33l K33r K35 K37 K38 K39 K40 K43; lia | clear - HV34l HV34r K33l K33r K35 K37 K38 K39 K40 K43; lia | clear - HV34l HV34r K33l K33r K35 K37 K38 K39 K40 K43; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K33l K33r K35 K37 K38 K39 K40 K43) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K33l K33r K35 K37 K38 K39 K40 K43) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K33l K33r K35 K37 K38 K39 K40 K43) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K32 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K33l K33r K35 K37 K38 K39 K40 K43) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K33l K33r K35 K37 K38 K39 K40 K43) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K33l K33r K35 K37 K38 K39 K40 K43; lia | clear - HV34l HV34r K33l K33r K35 K37 K38 K39 K40 K43; lia | exactA K41]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K33l K33r K35 K37 K38 K39 K40 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38) | evalEk ZA ltac:(clear - HV56l HV56r K45l K45r K46) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38; lia | byte_tac ltac:(clear - HV56l HV56r K45l K45r K46) | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K45l K45r K46) | exact (conj K45l K45r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV56l HV56r K45l K45r K46) | clear; lia | rewrite (L5K.land1_bit0_false vz_56 ltac:(clear - HV56l HV56r K45l K45r K46; lia) K46); clear; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvX5S.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvX5S.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_50 / 8) + 2147450880) + 20) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 20) + 2) -> ~ ((vz_50 + 160) <= bv_unsigned a < (vz_50 + 160) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PawvX5S.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvX5S.ps0) with 0xb13d8 in Hms. change (SR.ps_regs PawvX5S.ps0) with (map (fun i => (i, nth i PawvX5S.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvX5S.ps0) with PawvX5S.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvX5S.regs0 PawvX5S.regs_out0 80 KS_awvX5S KS_awvX5S_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvX5S.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvX5S.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX5S.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvX5S.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX5S.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvX5S.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX5S.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvX5S.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX5S.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvX5S.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX5S.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PawvX5S.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX5S.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PawvX5S.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk' ZA Hag ltac:(clear - HV56l HV56r K45l K45r K46) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K38) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K30 K31 K39 K43) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvX5L := LibSegBa_awvX5L_b.
Definition KS_awvX5L : list nat := Eval vm_compute in (BG.kept_list 80 PawvX5L.regs0 PawvX5L.regs_out0).
Lemma KS_awvX5L_ok : BG.kept_ok 80 PawvX5L.regs0 PawvX5L.regs_out0 KS_awvX5L = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvX5L_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 368) -> getr R (reg 24) = Z_to_bv 64 ((((V 33%nat) + 368) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 368) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 384) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 376) / 8) + 2147450880) 1 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 -> L5.writable RSEGS M (V 50%nat) 512 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) ->
  (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) -> 6905856 <= (V 34%nat) <= 140737488355320 ->
  aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 160) + 160 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 160)) ->
  ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> ((V 50%nat) + 512 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 50%nat)) -> ((V 51%nat) + 1 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 51%nat)) -> L5.u64_at RSEGS M (V 34%nat) 1251456 ->
  L5KA.zeros_at M 2147607327 1 -> ((((V 34%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 34%nat) / 8) + 2147450880)) -> L5.u8_at RSEGS M ((V 33%nat) + 368) (V 56%nat) -> 0 <= (V 56%nat) <= 255 ->
  Z.testbit (V 56%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 384) (V 57%nat) -> 4096 <= (V 57%nat) <= 140737488355320 -> aligned (V 57%nat) 8 ->
  L5.u64_at RSEGS M ((V 33%nat) + 376) (V 58%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 20) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 20) + 2) -> ~ (((V 50%nat) + 160) <= bv_unsigned a < ((V 50%nat) + 160) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 20) <= i < ((((V 50%nat) / 8) + 2147450880) + 20) + 2) -> ~ (((V 50%nat) + 160) <= i < ((V 50%nat) + 160) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb1054 M) (st fx' R' 0xb13d8 M')
        /\ (forall x, In x KS_awvX5L -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 725976
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 160)
        /\ getr R' (reg 12) = Z_to_bv 64 20
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 692916
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 168) (V 58%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 160) (V 57%nat)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450901) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450900) 0
        /\ L5.defined M' (V 50%nat) 160
        /\ L5.defined M' ((V 50%nat) + 176) 336).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 K13 K14 K15 pvzI12 K17 K18 K19 K20 K21 K22 pvzI13 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 pvzI14 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 pvzI15 K48 K49 pvzI16 K51 K52.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV58l; move HV58l before pvzI9; pose proof (proj2 pvzI9) as HV58r; move HV58r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K16l; move K16l before pvzI12; pose proof (proj2 pvzI12) as K16r; move K16r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K23l; move K23l before pvzI13; pose proof (proj2 pvzI13) as K23r; move K23r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K35l; move K35l before pvzI14; pose proof (proj2 pvzI14) as K35r; move K35r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K47l; move K47l before pvzI15; pose proof (proj2 pvzI15) as K47r; move K47r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K50l; move K50l before pvzI16; pose proof (proj2 pvzI16) as K50r; move K50r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PawvX5L.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvX5L.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvX5L.kn0).
  { unfold know_ok, PawvX5L.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K39) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K39) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K39) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K15 K27 K28 K39; lia | clear - HV2l HV2r K3l K3r K15 K27 K28 K39; lia | clear - HV2l HV2r K3l K3r K15 K27 K28 K39; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | exactA K12]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | exactA K13]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45; lia | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42; lia | clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42; lia | clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | clear; lia | exact K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45; lia | clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45; lia | clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K15 K27 K28 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K23l K23r K25 K26 K28 K30 K34 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45; lia | clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45; lia | exactA K43]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K35l K35r K37 K39 K40 K41 K42 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | evalEk ZA ltac:(clear - HV56l HV56r K47l K47r K48) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | byte_tac ltac:(clear - HV56l HV56r K47l K47r K48) | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K47l K47r K48) | exact (conj K47l K47r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV56l HV56r K47l K47r K48) | clear; lia | rewrite (L5K.land1_bit0_true vz_56 ltac:(clear - HV56l HV56r K47l K47r K48; lia) K48); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | evalEk ZA ltac:(clear - HV57l HV57r K50l K50r) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K50l K50r) | exact (conj K50l K50r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV57l HV57r K50l K50r) | clear; lia | exact K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | clear - HV33l HV33r K6l K6r K8 K15 K29 K30 K31 K40; lia | exactA K52]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvX5L.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvX5L.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_50 / 8) + 2147450880) + 20) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 20) + 2) -> ~ ((vz_50 + 160) <= bv_unsigned a < (vz_50 + 160) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PawvX5L.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvX5L.ps0) with 0xb13d8 in Hms. change (SR.ps_regs PawvX5L.ps0) with (map (fun i => (i, nth i PawvX5L.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvX5L.ps0) with PawvX5L.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvX5L.regs0 PawvX5L.regs_out0 80 KS_awvX5L KS_awvX5L_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvX5L.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvX5L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX5L.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvX5L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX5L.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvX5L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX5L.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvX5L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX5L.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvX5L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX5L.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PawvX5L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX5L.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PawvX5L.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk' ZA Hag ltac:(clear - HV58l HV58r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk' ZA Hag ltac:(clear - HV57l HV57r K50l K50r) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K16l K16r K20 K26 K27 K29 K31 K32 K33 K41 K45) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvX6 := LibSegBa_awvX6_b.
Definition KS_awvX6 : list nat := Eval vm_compute in (BG.kept_list 80 PawvX6.regs0 PawvX6.regs_out0).
Lemma KS_awvX6_ok : BG.kept_ok 80 PawvX6.regs0 PawvX6.regs_out0 KS_awvX6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvX6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 368) -> getr R (reg 24) = Z_to_bv 64 ((((V 33%nat) + 368) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  L5.writable RSEGS M ((V 33%nat) + 8) 1 -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb13d8 M) (st fx' R' 0x7b90c M')
        /\ (forall x, In x KS_awvX6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726080
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 1
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450901) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450900) 248
        /\ L5.defined M' ((V 50%nat) + 8) 504).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 pvzI9 K14 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvX6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvX6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvX6.kn0).
  { unfold know_ok, PawvX6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | clear - HV2l HV2r K3l K3r K12 K24 K25; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28; lia | byte_tac ltac:(clear) | exactA K33]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvX6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvX6.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 64) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PawvX6.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvX6.ps0) with 0x7b90c in Hms. change (SR.ps_regs PawvX6.ps0) with (map (fun i => (i, nth i PawvX6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvX6.ps0) with PawvX6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvX6.regs0 PawvX6.regs_out0 80 KS_awvX6 KS_awvX6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvX6.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvX6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvX6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvX6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvX6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvX6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PNARVXP.
