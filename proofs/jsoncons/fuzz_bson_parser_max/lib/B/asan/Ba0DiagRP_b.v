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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_drA_b LibSegBa_drB_b LibSegBa_drD_b LibSegBa_drDs_b LibSegBa_drEa_b LibSegBa_drFa_b LibSegBa_drGa_b LibSegBa_dfA_b LibSegBa_dfG_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module AS0DIAGRP.
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
Lemma rdn_cons1u : forall (MV : word -> option byte) a b (n : nat) bs,
  rdn RSEGS MV (Z_to_bv 64 a) 1 = Some [b] -> rdn RSEGS MV (Z_to_bv 64 (a + 1)) n = Some bs ->
  rdn RSEGS MV (Z_to_bv 64 a) (Datatypes.S n) = Some (b :: bs).
Proof.
  intros MV a b n bs H1 H2. change (Datatypes.S n) with (1 + n)%nat. change (b :: bs) with ([b] ++ bs).
  apply (SeqExec.rdn_app RSEGS MV 1%nat n _ _ _ H1).
  replace (Z_to_bv 64 a + nat_to_word 1)%bv with (Z_to_bv 64 (a + 1)); [exact H2|].
  apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma u32_of_u8x4 M a v : 0 <= v < 2 ^ 32 ->
  L5.u8_at RSEGS M a (v mod 256) -> L5.u8_at RSEGS M (a + 1) ((v / 256) mod 256) ->
  L5.u8_at RSEGS M (a + 2) ((v / 65536) mod 256) -> L5.u8_at RSEGS M (a + 3) ((v / 16777216) mod 256) ->
  L5.u32_at RSEGS M a v.
Proof.
  intros Hv B0 B1 B2 B3. unfold L5.u8_at, L5.u32_at in *.
  replace (word_to_le_bytes 4 (Z_to_bv 64 v)) with
    [Z_to_bv 8 (v mod 256); Z_to_bv 8 ((v / 256) mod 256); Z_to_bv 8 ((v / 65536) mod 256); Z_to_bv 8 ((v / 16777216) mod 256)].
  - apply (rdn_cons1u M a _ 3 _ B0). apply (rdn_cons1u M (a + 1) _ 2 _ B1).
    replace (a + 1 + 1) with (a + 2) by lia. apply (rdn_cons1u M (a + 2) _ 1 _ B2).
    replace (a + 2 + 1) with (a + 3) by lia. exact B3.
  - unfold word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small v (2 ^ 64)) by lia. cbn [Z_to_le_bytes].
    repeat (apply (f_equal2 (@cons _)); [apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
      rewrite ?Z.shiftr_shiftr by lia; rewrite ?Z.shiftr_div_pow2 by lia; cbn [Z.add Pos.add];
      try change (2 ^ 8) with 256; try change (2 ^ 16) with 65536; try change (2 ^ 24) with 16777216;
      rewrite ?Z.mod_mod by lia; reflexivity|]); reflexivity.
Qed.
Lemma u8x4_of_u32 M a v : 0 <= v < 2 ^ 32 -> L5.u32_at RSEGS M a v ->
  L5.u8_at RSEGS M a (v mod 256) /\ L5.u8_at RSEGS M (a + 1) ((v / 256) mod 256) /\
  L5.u8_at RSEGS M (a + 2) ((v / 65536) mod 256) /\ L5.u8_at RSEGS M (a + 3) ((v / 16777216) mod 256).
Proof.
  intros Hv H. unfold L5.u32_at, L5.u8_at in *.
  replace (word_to_le_bytes 4 (Z_to_bv 64 v)) with
    [Z_to_bv 8 (v mod 256); Z_to_bv 8 ((v / 256) mod 256); Z_to_bv 8 ((v / 65536) mod 256); Z_to_bv 8 ((v / 16777216) mod 256)] in H.
  - assert (AE : forall j : nat, (Z_to_bv 64 a + nat_to_word j)%bv = Z_to_bv 64 (a + Z.of_nat j)).
    { intros j. apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity. }
    pose proof (SeqExec.rdn_nth RSEGS M 4 _ _ 0 H ltac:(lia)) as B0.
    pose proof (SeqExec.rdn_nth RSEGS M 4 _ _ 1 H ltac:(lia)) as B1.
    pose proof (SeqExec.rdn_nth RSEGS M 4 _ _ 2 H ltac:(lia)) as B2.
    pose proof (SeqExec.rdn_nth RSEGS M 4 _ _ 3 H ltac:(lia)) as B3.
    rewrite AE in B0, B1, B2, B3. cbn [nth] in B0, B1, B2, B3.
    change (Z.of_nat 0) with 0 in B0. change (Z.of_nat 1) with 1 in B1. change (Z.of_nat 2) with 2 in B2.
    change (Z.of_nat 3) with 3 in B3. replace (a + 0) with a in B0 by lia.
    repeat split; assumption.
  - unfold word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small v (2 ^ 64)) by lia. cbn [Z_to_le_bytes].
    repeat (apply (f_equal2 (@cons _)); [apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
      rewrite ?Z.shiftr_shiftr by lia; rewrite ?Z.shiftr_div_pow2 by lia; cbn [Z.add Pos.add];
      try change (2 ^ 8) with 256; try change (2 ^ 16) with 65536; try change (2 ^ 24) with 16777216;
      rewrite ?Z.mod_mod by lia; reflexivity|]); reflexivity.
Qed.
Lemma u8_of_u32_cell E M b off e a v a' k bk : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 2 ^ 32 -> 0 <= k < 4 -> a' = a + off + k -> bk = (v / 2 ^ (8 * k)) mod 256 ->
  L5.u8_at RSEGS M a' bk.
Proof.
  intros K Ha Hv Hr Hk -> ->. pose proof (u8x4_of_u32 M (a + off) v Hr (L5K.u32_of_KWord4 RSEGS E M b off e a v K Ha Hv)) as (U0 & U1 & U2 & U3).
  assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3) as [-> | [-> | [-> | ->]]] by lia.
  - replace (a + off + 0) with (a + off) by lia. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r. exact U0.
  - change (2 ^ (8 * 1)) with 256. exact U1.
  - change (2 ^ (8 * 2)) with 65536. exact U2.
  - change (2 ^ (8 * 3)) with 16777216. exact U3.
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
Module PdrA := LibSegBa_drA_b.
Definition KS_drA : list nat := Eval vm_compute in (BG.kept_list 140 PdrA.regs0 PdrA.regs_out0).
Lemma KS_drA_ok : BG.kept_ok 140 PdrA.regs0 PdrA.regs_out0 KS_drA = true. Proof. vm_compute. reflexivity. Qed.
Lemma drA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 687464 -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 1293512 -> getr R (reg 11) = Z_to_bv 64 127251 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 2352) 2352 -> L5.defined M ((V 2%nat) - 2352) 2352 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 1 <= (V 34%nat) <= 1 -> (((V 2%nat) - 2352) + 2352 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 2352)) ->
  L5.u64_at RSEGS M 2147466776 0 -> L5.u64_at RSEGS M 2147466784 0 -> L5.u8_at RSEGS M 1313048 1 -> L5.u8_at RSEGS M 1906620 1 ->
  L5.u64_at RSEGS M 1309752 2147450880 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 2352) <= bv_unsigned a < ((V 2%nat) - 2352) + 2352) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 2352) <= i < ((V 2%nat) - 2352) + 2352) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x633bc M) (st fx' R' 0x674b0 M')
        /\ (forall x, In x KS_drA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 422824
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 2352)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 9) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 115
        /\ getr R' (reg 13) = Z_to_bv 64 115
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 10
        /\ getr R' (reg 19) = Z_to_bv 64 127272
        /\ getr R' (reg 20) = Z_to_bv 64 88935
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 40)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 9
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 2%nat) - 2296)
        /\ getr R' (reg 25) = Z_to_bv 64 12297829382473034410
        /\ getr R' (reg 26) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 27) = Z_to_bv 64 37
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2292) 115
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2304) 127272
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2296) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2312) 127270
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2320) 18446744073709551615
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2289) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2290) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2291) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2293) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2294) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2295) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2321) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2322) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2323) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2324) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2325) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2326) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2327) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2328) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2344) ((V 2%nat) - 232)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2336) 133306
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 2%nat) - 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 1293512
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 127251
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 426800
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 2%nat) - 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 2%nat) - 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) ((V 2%nat) - 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 15)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 14)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 13)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 17)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 16)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 687464
        /\ L5.defined M' ((V 2%nat) - 2352) 8
        /\ L5.defined M' ((V 2%nat) - 2288) 2072
        /\ L5.defined M' ((V 2%nat) - 112) 8).
Proof.
  intros pvzI1 pvzI2 pvzI3 G1 G2 G10 G11 G12 pvzI4 K1 K2 K3 K4 pvzI5 pvzI6 K7 K8 K9 K10 K11 K12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K5l; move K5l before pvzI5; pose proof (proj2 pvzI5) as K5r; move K5r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PdrA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdrA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdrA.kn0).
  { unfold know_ok, PdrA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K12]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdrA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdrA.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 2352) <= bv_unsigned a < (vz_2 - 2352) + 2352) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdrA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdrA.ps0) with 0x674b0 in Hms. change (SR.ps_regs PdrA.ps0) with (map (fun i => (i, nth i PdrA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdrA.ps0) with PdrA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdrA.regs0 PdrA.regs_out0 140 KS_drA KS_drA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrA.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PdrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 16); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 17); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 18); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 29); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 30); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 31); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 32); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 34); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 35); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 36); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 37); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 38); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 39); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 40); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 41); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 42); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 43); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 44); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 45); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 46); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 47); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 48); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 49); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdrB := LibSegBa_drB_b.
Definition KS_drB : list nat := Eval vm_compute in (BG.kept_list 140 PdrB.regs0 PdrB.regs_out0).
Lemma KS_drB_ok : BG.kept_ok 140 PdrB.regs0 PdrB.regs_out0 KS_drB = true. Proof. vm_compute. reflexivity. Qed.
Lemma drB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 20%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 23%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 25%nat) < 2 ^ 64 -> 0 <= (V 26%nat) < 2 ^ 64 -> 0 <= (V 27%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 120%nat) < 2 ^ 64 -> 0 <= (V 121%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 -> 0 <= (V 123%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) + 2240) -> getr R (reg 19) = Z_to_bv 64 127272 -> getr R (reg 20) = Z_to_bv 64 (V 120%nat) -> getr R (reg 21) = Z_to_bv 64 (V 121%nat) -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) -> getr R (reg 23) = Z_to_bv 64 (V 123%nat) -> getr R (reg 24) = Z_to_bv 64 ((V 2%nat) + 56) -> getr R (reg 25) = Z_to_bv 64 12297829382473034410 -> getr R (reg 26) = Z_to_bv 64 18446744073709551615 -> getr R (reg 27) = Z_to_bv 64 37 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 896) 3136 -> L5.defined M ((V 2%nat) - 896) 3136 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 1 <= (V 34%nat) <= 1 -> (((V 2%nat) - 896) + 3136 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 896)) ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147451102) 32 -> L5.u64_at RSEGS M 2147466776 0 -> L5.u64_at RSEGS M 2147466784 0 -> L5.writable RSEGS M 1293512 4 ->
  L5.writable RSEGS M 1293520 8 -> L5.writable RSEGS M 1293528 8 -> L5.writable RSEGS M 1293544 8 -> L5.writable RSEGS M 1293552 8 ->
  L5.writable RSEGS M 1293568 8 -> L5.writable RSEGS M 1293600 8 -> L5.writable RSEGS M 1293608 8 -> L5.writable RSEGS M 1293648 4 ->
  L5.u64_at RSEGS M ((V 2%nat) + 2232) 426800 -> L5.u64_at RSEGS M ((V 2%nat) + 2224) 127251 -> L5.u64_at RSEGS M ((V 2%nat) + 2216) 1293512 -> L5.u64_at RSEGS M ((V 2%nat) + 2208) ((V 2%nat) + 2304) ->
  L5.u64_at RSEGS M ((V 2%nat) + 2200) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2192) (V 20%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2184) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2176) (V 22%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 2168) (V 23%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2160) (V 24%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2152) (V 25%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2144) (V 26%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 2136) (V 27%nat) -> L5.u64_at RSEGS M 1282896 1184024 -> L5.u64_at RSEGS M ((V 2%nat) + 2264) ((V 2%nat) + 2304) -> L5.u64_at RSEGS M 6896960 (V 40%nat) ->
  L5.u32_at RSEGS M 1293652 4294967295 -> L5.u32_at RSEGS M 1293512 5 -> L5.u64_at RSEGS M 1293608 0 -> L5.u64_at RSEGS M 1293600 6898968 ->
  L5.u32_at RSEGS M 1293648 0 -> L5.u32_at RSEGS M 1293656 4294967295 -> L5.u8_at RSEGS M 1313049 1 -> L5.u64_at RSEGS M 1309752 2147450880 ->
  L5.u64_at RSEGS M 1283272 1218816 -> L5.u64_at RSEGS M ((V 2%nat) + 2304) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 896) <= bv_unsigned a < ((V 2%nat) - 896) + 3136) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293520 <= bv_unsigned a < 1293520 + 8) -> ~ (1293528 <= bv_unsigned a < 1293528 + 8) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> ~ (1293648 <= bv_unsigned a < 1293648 + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 896) <= i < ((V 2%nat) - 896) + 3136) -> ~ (1293512 <= i < 1293512 + 4) -> ~ (1293520 <= i < 1293520 + 8) -> ~ (1293528 <= i < 1293528 + 8) -> ~ (1293544 <= i < 1293544 + 8) -> ~ (1293552 <= i < 1293552 + 8) -> ~ (1293568 <= i < 1293568 + 8) -> ~ (1293600 <= i < 1293600 + 8) -> ~ (1293608 <= i < 1293608 + 8) -> ~ (1293648 <= i < 1293648 + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x67414 M) (st fx' R' 0x63370 M')
        /\ (forall x, In x KS_drB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1186016
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 1328)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 37
        /\ getr R' (reg 9) = Z_to_bv 64 2147483647
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 2147483647
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) + 1872)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) + 2312)
        /\ getr R' (reg 14) = Z_to_bv 64 31
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551558
        /\ getr R' (reg 16) = Z_to_bv 64 115
        /\ getr R' (reg 17) = Z_to_bv 64 8
        /\ getr R' (reg 18) = Z_to_bv 64 2147483628
        /\ getr R' (reg 19) = Z_to_bv 64 19
        /\ getr R' (reg 20) = Z_to_bv 64 1293512
        /\ getr R' (reg 21) = Z_to_bv 64 127272
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 26) = Z_to_bv 64 0
        /\ getr R' (reg 27) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1440) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1872) ((V 2%nat) + 2312)
        /\ L5.u64_at RSEGS M' 1293552 ((V 2%nat) + 1907)
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1906) 32
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1905) 110
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1904) 111
        /\ L5.u32_at RSEGS M' ((V 2%nat) + 1900) 544370546
        /\ L5.u32_at RSEGS M' ((V 2%nat) + 1896) 1919230052
        /\ L5.u32_at RSEGS M' ((V 2%nat) + 1892) 1634038304
        /\ L5.u32_at RSEGS M' ((V 2%nat) + 1888) 979987555
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1368) 18446744072850558157
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1376) 18446744073709486079
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1432) 214748364
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1408) 75913
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1760) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1424) 6896960
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1416) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1400) ((V 2%nat) + 1872)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1384) ((V 2%nat) + 1968)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1392) ((V 2%nat) + 2136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1768) (V 27%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1776) (V 26%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1784) (V 25%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1792) (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1800) (V 23%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1808) (V 22%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1816) 5
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1824) 6898968
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1832) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1840) 6896960
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1848) 127251
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1856) 1293512
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1864) 1184288
        /\ L5.u64_at RSEGS M' 1293544 ((V 2%nat) + 1968)
        /\ L5.u64_at RSEGS M' 1293528 0
        /\ L5.u64_at RSEGS M' 1293520 0
        /\ L5.u64_at RSEGS M' 1293568 ((V 2%nat) + 1888)
        /\ L5.u32_at RSEGS M' 1293648 18446744073709551615
        /\ L5.u64_at RSEGS M' 1293608 80
        /\ L5.u64_at RSEGS M' 1293600 ((V 2%nat) + 1888)
        /\ L5.u32_at RSEGS M' 1293512 5
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2160) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2152) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2144) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2136) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2168) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1880) ((V 2%nat) + 2304)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2176) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2184) (V 21%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2192) (V 20%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2200) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2208) ((V 2%nat) + 2304)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2216) 1293512
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2224) 127251
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2232) 426864
        /\ L5.defined M' ((V 2%nat) + 1328) 40
        /\ L5.defined M' ((V 2%nat) + 1448) 312
        /\ L5.defined M' ((V 2%nat) + 1907) 229).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI18 K1 K2 K3 K4 pvzI19 pvzI20 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV20l; move HV20l before pvzI3; pose proof (proj2 pvzI3) as HV20r; move HV20r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV21l; move HV21l before pvzI4; pose proof (proj2 pvzI4) as HV21r; move HV21r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV22l; move HV22l before pvzI5; pose proof (proj2 pvzI5) as HV22r; move HV22r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV23l; move HV23l before pvzI6; pose proof (proj2 pvzI6) as HV23r; move HV23r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV24l; move HV24l before pvzI7; pose proof (proj2 pvzI7) as HV24r; move HV24r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV25l; move HV25l before pvzI8; pose proof (proj2 pvzI8) as HV25r; move HV25r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV26l; move HV26l before pvzI9; pose proof (proj2 pvzI9) as HV26r; move HV26r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV27l; move HV27l before pvzI10; pose proof (proj2 pvzI10) as HV27r; move HV27r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV33l; move HV33l before pvzI11; pose proof (proj2 pvzI11) as HV33r; move HV33r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV34l; move HV34l before pvzI12; pose proof (proj2 pvzI12) as HV34r; move HV34r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV40l; move HV40l before pvzI13; pose proof (proj2 pvzI13) as HV40r; move HV40r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV120l; move HV120l before pvzI14; pose proof (proj2 pvzI14) as HV120r; move HV120r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV121l; move HV121l before pvzI15; pose proof (proj2 pvzI15) as HV121r; move HV121r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV122l; move HV122l before pvzI16; pose proof (proj2 pvzI16) as HV122r; move HV122r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV123l; move HV123l before pvzI17; pose proof (proj2 pvzI17) as HV123r; move HV123r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K5l; move K5l before pvzI19; pose proof (proj2 pvzI19) as K5r; move K5r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K6l; move K6l before pvzI20; pose proof (proj2 pvzI20) as K6r; move K6r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_20 := V 20%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_22 := V 22%nat) in *. set (vz_23 := V 23%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_25 := V 25%nat) in *. set (vz_26 := V 26%nat) in *. set (vz_27 := V 27%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_120 := V 120%nat) in *. set (vz_121 := V 121%nat) in *. set (vz_122 := V 122%nat) in *. set (vz_123 := V 123%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 20%nat => Z_to_bv 64 vz_20 | 21%nat => Z_to_bv 64 vz_21 | 22%nat => Z_to_bv 64 vz_22 | 23%nat => Z_to_bv 64 vz_23 | 24%nat => Z_to_bv 64 vz_24 | 25%nat => Z_to_bv 64 vz_25 | 26%nat => Z_to_bv 64 vz_26 | 27%nat => Z_to_bv 64 vz_27 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 40%nat => Z_to_bv 64 vz_40 | 120%nat => Z_to_bv 64 vz_120 | 121%nat => Z_to_bv 64 vz_121 | 122%nat => Z_to_bv 64 vz_122 | 123%nat => Z_to_bv 64 vz_123 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 20%nat => vz_20 | 21%nat => vz_21 | 22%nat => vz_22 | 23%nat => vz_23 | 24%nat => vz_24 | 25%nat => vz_25 | 26%nat => vz_26 | 27%nat => vz_27 | 33%nat => vz_33 | 34%nat => vz_34 | 40%nat => vz_40 | 120%nat => vz_120 | 121%nat => vz_121 | 122%nat => vz_122 | 123%nat => vz_123 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 124%nat. }
  assert (HR: regs_ok E PdrB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdrB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdrB.kn0).
  { unfold know_ok, PdrB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV20l HV20r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV22l HV22r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV23l HV23r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV25l HV25r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV26l HV26r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV27l HV27r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K45]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdrB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdrB.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 896) <= bv_unsigned a < (vz_2 - 896) + 3136) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293520 <= bv_unsigned a < 1293520 + 8) -> ~ (1293528 <= bv_unsigned a < 1293528 + 8) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> ~ (1293648 <= bv_unsigned a < 1293648 + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8 Hn9. apply Hfr. unfold PdrB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn6; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn7; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn8; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn9; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8 Hn9. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdrB.ps0) with 0x63370 in Hms. change (SR.ps_regs PdrB.ps0) with (map (fun i => (i, nth i PdrB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdrB.ps0) with PdrB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdrB.regs0 PdrB.regs_out0 140 KS_drB KS_drB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrB.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PdrB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { apply u32_of_u8x4; [clear; lia | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia] | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia] | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia] | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]]. }
  split. { apply u32_of_u8x4; [clear; lia | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia] | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia] | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia] | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]]. }
  split. { apply u32_of_u8x4; [clear; lia | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 17); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia] | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 16); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia] | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia] | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]]. }
  split. { apply u32_of_u8x4; [clear; lia | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 21); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia] | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 20); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia] | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 19); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia] | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 18); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 29); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 30); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 31); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 32); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV27l HV27r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV26l HV26r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 34); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV25l HV25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 35); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV24l HV24r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 36); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV23l HV23r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 37); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV22l HV22r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 38); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 39); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 40); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 41); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 42); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 43); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 44); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 45); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 46); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 47); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 48); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 49); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 50); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 51); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 52); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 53); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 54); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 55); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 56); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 57); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 58); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 59); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 60); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV21l HV21r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 61); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV20l HV20r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 62); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 63); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 64); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 65); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 66); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 67); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 68); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 69); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdrD := LibSegBa_drD_b.
Definition KS_drD : list nat := Eval vm_compute in (BG.kept_list 140 PdrD.regs0 PdrD.regs_out0).
Lemma KS_drD_ok : BG.kept_ok 140 PdrD.regs0 PdrD.regs_out0 KS_drD = true. Proof. vm_compute. reflexivity. Qed.
Lemma drD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 37 -> getr R (reg 9) = Z_to_bv 64 2147483647 -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 2147483628 -> getr R (reg 19) = Z_to_bv 64 19 -> getr R (reg 20) = Z_to_bv 64 1293512 -> getr R (reg 21) = Z_to_bv 64 127272 -> getr R (reg 22) = Z_to_bv 64 0 -> getr R (reg 23) = Z_to_bv 64 (V 33%nat) -> getr R (reg 25) = Z_to_bv 64 18446744073709551615 -> getr R (reg 26) = Z_to_bv 64 0 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 2224) 2272 -> L5.defined M ((V 2%nat) - 2224) 2272 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 1 <= (V 34%nat) <= 1 -> (((V 2%nat) - 2224) + 2272 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 2224)) ->
  L5.writable RSEGS M 1293552 8 -> L5.u8_at RSEGS M 1293512 5 -> L5.u64_at RSEGS M 1293544 ((V 2%nat) + 640) -> L5.u64_at RSEGS M 1293552 ((V 2%nat) + 579) ->
  L5.u32_at RSEGS M 1293656 4294967295 -> L5.u8_at RSEGS M 1313049 1 -> L5.u64_at RSEGS M 1283272 1218816 -> L5.u8_at RSEGS M ((V 33%nat) + 1) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 2224) <= bv_unsigned a < ((V 2%nat) - 2224) + 2272) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 2224) <= i < ((V 2%nat) - 2224) + 2272) -> ~ (1293552 <= i < 1293552 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x1218e0 M) (st fx' R' 0x121e2c M')
        /\ (forall x, In x KS_drD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1187080
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 1293512
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) + 579)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 3
        /\ getr R' (reg 18) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 1
        /\ getr R' (reg 26) = Z_to_bv 64 1
        /\ getr R' (reg 27) = Z_to_bv 64 1
        /\ L5.u64_at RSEGS M' 1293552 ((V 2%nat) + 579)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 32) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 16) 1
        /\ L5.u64_at RSEGS M' (V 2%nat) 69053
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 24) 0
        /\ L5.defined M' ((V 2%nat) + 40) 8).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G25 G26 pvzI4 K1 K2 K3 K4 pvzI5 pvzI6 K7 K8 K9 K10 K11 K12 K13 K14 K15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K5l; move K5l before pvzI5; pose proof (proj2 pvzI5) as K5r; move K5r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PdrD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdrD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdrD.kn0).
  { unfold know_ok, PdrD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K5l K5r K7; lia | clear - HV33l HV33r K5l K5r K7; lia | byte_tac ltac:(clear) | exactA K15]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdrD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdrD.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 2224) <= bv_unsigned a < (vz_2 - 2224) + 2272) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PdrD.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdrD.ps0) with 0x121e2c in Hms. change (SR.ps_regs PdrD.ps0) with (map (fun i => (i, nth i PdrD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdrD.ps0) with PdrD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdrD.regs0 PdrD.regs_out0 140 KS_drD KS_drD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdrD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PdrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrD.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrD.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrD.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrD.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrD.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PdrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrD.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PdrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrD.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PdrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrD.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PdrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrD.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PdrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrD.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PdrD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdrDs := LibSegBa_drDs_b.
Definition KS_drDs : list nat := Eval vm_compute in (BG.kept_list 140 PdrDs.regs0 PdrDs.regs_out0).
Lemma KS_drDs_ok : BG.kept_ok 140 PdrDs.regs0 PdrDs.regs_out0 KS_drDs = true. Proof. vm_compute. reflexivity. Qed.
Lemma drDs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 37 -> getr R (reg 9) = Z_to_bv 64 2147483647 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 1 -> getr R (reg 12) = Z_to_bv 64 1293512 -> getr R (reg 18) = Z_to_bv 64 0 -> getr R (reg 19) = Z_to_bv 64 19 -> getr R (reg 20) = Z_to_bv 64 1293512 -> getr R (reg 21) = Z_to_bv 64 127272 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.defined M ((V 2%nat) - 64) 64 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 1 <= (V 34%nat) <= 1 -> (((V 2%nat) - 64) + 64 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 64)) ->
  L5.u64_at RSEGS M 1293544 ((V 2%nat) + 640) -> L5.u64_at RSEGS M 1293552 ((V 2%nat) + 579) -> L5.u32_at RSEGS M 1293656 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x121e2c M) (st fx' R' 0x77c90 M')
        /\ (forall x, In x KS_drDs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1182924
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 1293512
        /\ getr R' (reg 9) = Z_to_bv 64 1
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) + 579)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 127272
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 1293512
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 19
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) 2147483647
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) 37
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) 1187376
        /\ L5.defined M' ((V 2%nat) - 64) 8).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 pvzI4 K1 K2 K3 K4 pvzI5 pvzI6 K7 K8 K9 K10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K5l; move K5l before pvzI5; pose proof (proj2 pvzI5) as K5r; move K5r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PdrDs.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdrDs.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdrDs.kn0).
  { unfold know_ok, PdrDs.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K10]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdrDs.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdrDs.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 64) <= bv_unsigned a < (vz_2 - 64) + 64) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PdrDs.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdrDs.ps0) with 0x77c90 in Hms. change (SR.ps_regs PdrDs.ps0) with (map (fun i => (i, nth i PdrDs.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdrDs.ps0) with PdrDs.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdrDs.regs0 PdrDs.regs_out0 140 KS_drDs KS_drDs_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdrDs.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PdrDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrDs.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PdrDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrDs.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PdrDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrDs.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PdrDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrDs.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdrDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrDs.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdrDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrDs.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdrDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrDs.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PdrDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrDs.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PdrDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdrEa := LibSegBa_drEa_b.
Definition KS_drEa : list nat := Eval vm_compute in (BG.kept_list 140 PdrEa.regs0 PdrEa.regs_out0).
Lemma KS_drEa_ok : BG.kept_ok 140 PdrEa.regs0 PdrEa.regs_out0 KS_drEa = true. Proof. vm_compute. reflexivity. Qed.
Lemma drEa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 1293512 -> getr R (reg 9) = Z_to_bv 64 1 -> getr R (reg 19) = Z_to_bv 64 0 -> getr R (reg 26) = Z_to_bv 64 1 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 80 -> L5.defined M ((V 2%nat) - 16) 80 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 1 <= (V 34%nat) <= 1 -> (((V 2%nat) - 16) + 80 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.writable RSEGS M 1293552 8 -> L5.u64_at RSEGS M 1293552 ((V 2%nat) + 643) -> L5.u64_at RSEGS M ((V 2%nat) + 56) 1187376 -> L5.u64_at RSEGS M ((V 2%nat) + 48) 37 ->
  L5.u64_at RSEGS M ((V 2%nat) + 40) 2147483647 -> L5.u64_at RSEGS M ((V 2%nat) + 32) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 24) 19 -> L5.u64_at RSEGS M ((V 2%nat) + 16) 1293512 ->
  L5.u64_at RSEGS M ((V 2%nat) + 8) 127272 -> L5.u8_at RSEGS M 1293512 5 -> L5.u64_at RSEGS M 1293544 ((V 2%nat) + 704) -> L5.u32_at RSEGS M 1293656 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 80) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 80) -> ~ (1293552 <= i < 1293552 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x120ccc M) (st fx' R' 0x77c90 M')
        /\ (forall x, In x KS_drEa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1182924
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) + 644)
        /\ getr R' (reg 11) = Z_to_bv 64 127272
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 127272
        /\ getr R' (reg 20) = Z_to_bv 64 1293512
        /\ getr R' (reg 21) = Z_to_bv 64 127273
        /\ getr R' (reg 22) = Z_to_bv 64 1
        /\ getr R' (reg 23) = Z_to_bv 64 127272
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) 127273
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 16) 1293512
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 24) 20
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 32) 2147483627
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 40) 2147483647
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 48) 37
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 56) 1184784
        /\ L5.u64_at RSEGS M' 1293552 ((V 2%nat) + 644)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G9 G19 G26 pvzI4 K1 K2 K3 K4 pvzI5 pvzI6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K5l; move K5l before pvzI5; pose proof (proj2 pvzI5) as K5r; move K5r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PdrEa.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdrEa.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdrEa.kn0).
  { unfold know_ok, PdrEa.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K19]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdrEa.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdrEa.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 80) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PdrEa.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdrEa.ps0) with 0x77c90 in Hms. change (SR.ps_regs PdrEa.ps0) with (map (fun i => (i, nth i PdrEa.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdrEa.ps0) with PdrEa.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdrEa.regs0 PdrEa.regs_out0 140 KS_drEa KS_drEa_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdrEa.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PdrEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrEa.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdrEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrEa.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdrEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrEa.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdrEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrEa.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PdrEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrEa.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdrEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrEa.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdrEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrEa.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PdrEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrEa.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PdrEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdrFa := LibSegBa_drFa_b.
Definition KS_drFa : list nat := Eval vm_compute in (BG.kept_list 140 PdrFa.regs0 PdrFa.regs_out0).
Lemma KS_drFa_ok : BG.kept_ok 140 PdrFa.regs0 PdrFa.regs_out0 KS_drFa = true. Proof. vm_compute. reflexivity. Qed.
Lemma drFa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 23%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 25%nat) < 2 ^ 64 -> 0 <= (V 26%nat) < 2 ^ 64 -> 0 <= (V 27%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 123%nat) < 2 ^ 64 -> 0 <= (V 124%nat) < 2 ^ 64 -> 0 <= (V 125%nat) < 2 ^ 64 -> 0 <= (V 127%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 1293512 -> getr R (reg 9) = Z_to_bv 64 1 -> getr R (reg 19) = Z_to_bv 64 0 -> getr R (reg 22) = Z_to_bv 64 1 -> getr R (reg 23) = Z_to_bv 64 (V 123%nat) -> getr R (reg 24) = Z_to_bv 64 (V 124%nat) -> getr R (reg 25) = Z_to_bv 64 (V 125%nat) -> getr R (reg 26) = Z_to_bv 64 1 -> getr R (reg 27) = Z_to_bv 64 (V 127%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 624 -> L5.defined M ((V 2%nat) - 16) 624 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 1 <= (V 34%nat) <= 1 -> (((V 2%nat) - 16) + 624 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.writable RSEGS M 1293552 8 -> L5.u64_at RSEGS M 1293552 ((V 2%nat) + 644) -> L5.u64_at RSEGS M ((V 2%nat) + 56) 1184784 -> L5.u64_at RSEGS M ((V 2%nat) + 48) 37 ->
  L5.u64_at RSEGS M ((V 2%nat) + 40) 2147483647 -> L5.u64_at RSEGS M ((V 2%nat) + 32) 2147483627 -> L5.u64_at RSEGS M ((V 2%nat) + 24) 20 -> L5.u64_at RSEGS M ((V 2%nat) + 16) 1293512 ->
  L5.u64_at RSEGS M ((V 2%nat) + 8) 127273 -> L5.u64_at RSEGS M ((V 2%nat) + 160) 6896960 -> L5.u64_at RSEGS M 6896960 (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 496) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 600) 1184288 -> L5.u64_at RSEGS M ((V 2%nat) + 592) 1293512 -> L5.u64_at RSEGS M ((V 2%nat) + 584) 127251 -> L5.u64_at RSEGS M ((V 2%nat) + 576) 6896960 ->
  L5.u64_at RSEGS M ((V 2%nat) + 568) 1 -> L5.u64_at RSEGS M ((V 2%nat) + 560) 6898968 -> L5.u64_at RSEGS M ((V 2%nat) + 552) 5 -> L5.u64_at RSEGS M ((V 2%nat) + 544) (V 22%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 536) (V 23%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 528) (V 24%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 520) (V 25%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 512) (V 26%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 504) (V 27%nat) -> L5.u64_at RSEGS M 1293584 1180112 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 624) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 624) -> ~ (1293552 <= i < 1293552 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x120ccc M) (st fx' R' 0x12020c M')
        /\ (forall x, In x KS_drFa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1184320
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 496)
        /\ getr R' (reg 8) = Z_to_bv 64 0
        /\ getr R' (reg 9) = Z_to_bv 64 1293512
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 1180112
        /\ getr R' (reg 18) = Z_to_bv 64 6896960
        /\ getr R' (reg 19) = Z_to_bv 64 1
        /\ getr R' (reg 20) = Z_to_bv 64 6898968
        /\ getr R' (reg 21) = Z_to_bv 64 6896960
        /\ getr R' (reg 22) = Z_to_bv 64 (V 22%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 23%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 25%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 26%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 27%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 536) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 544) (V 22%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 552) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 560) 6898968
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 568) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 576) 6896960
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 584) 21
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 592) 1293512
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 600) 1184320
        /\ L5.u64_at RSEGS M' 1293552 ((V 2%nat) + 645)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 496) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 528) (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 520) (V 25%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 512) (V 26%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 504) (V 27%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 G2 G8 G9 G19 G22 G23 G24 G25 G26 G27 pvzI15 K1 K2 K3 K4 pvzI16 pvzI17 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV22l; move HV22l before pvzI2; pose proof (proj2 pvzI2) as HV22r; move HV22r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV23l; move HV23l before pvzI3; pose proof (proj2 pvzI3) as HV23r; move HV23r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV24l; move HV24l before pvzI4; pose proof (proj2 pvzI4) as HV24r; move HV24r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV25l; move HV25l before pvzI5; pose proof (proj2 pvzI5) as HV25r; move HV25r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV26l; move HV26l before pvzI6; pose proof (proj2 pvzI6) as HV26r; move HV26r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV27l; move HV27l before pvzI7; pose proof (proj2 pvzI7) as HV27r; move HV27r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV33l; move HV33l before pvzI8; pose proof (proj2 pvzI8) as HV33r; move HV33r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV34l; move HV34l before pvzI9; pose proof (proj2 pvzI9) as HV34r; move HV34r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV123l; move HV123l before pvzI11; pose proof (proj2 pvzI11) as HV123r; move HV123r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV124l; move HV124l before pvzI12; pose proof (proj2 pvzI12) as HV124r; move HV124r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV125l; move HV125l before pvzI13; pose proof (proj2 pvzI13) as HV125r; move HV125r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV127l; move HV127l before pvzI14; pose proof (proj2 pvzI14) as HV127r; move HV127r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K0l; move K0l before pvzI15; pose proof (proj2 pvzI15) as K0r; move K0r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K5l; move K5l before pvzI16; pose proof (proj2 pvzI16) as K5r; move K5r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K6l; move K6l before pvzI17; pose proof (proj2 pvzI17) as K6r; move K6r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_22 := V 22%nat) in *. set (vz_23 := V 23%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_25 := V 25%nat) in *. set (vz_26 := V 26%nat) in *. set (vz_27 := V 27%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_123 := V 123%nat) in *. set (vz_124 := V 124%nat) in *. set (vz_125 := V 125%nat) in *. set (vz_127 := V 127%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 22%nat => Z_to_bv 64 vz_22 | 23%nat => Z_to_bv 64 vz_23 | 24%nat => Z_to_bv 64 vz_24 | 25%nat => Z_to_bv 64 vz_25 | 26%nat => Z_to_bv 64 vz_26 | 27%nat => Z_to_bv 64 vz_27 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 40%nat => Z_to_bv 64 vz_40 | 123%nat => Z_to_bv 64 vz_123 | 124%nat => Z_to_bv 64 vz_124 | 125%nat => Z_to_bv 64 vz_125 | 127%nat => Z_to_bv 64 vz_127 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 22%nat => vz_22 | 23%nat => vz_23 | 24%nat => vz_24 | 25%nat => vz_25 | 26%nat => vz_26 | 27%nat => vz_27 | 33%nat => vz_33 | 34%nat => vz_34 | 40%nat => vz_40 | 123%nat => vz_123 | 124%nat => vz_124 | 125%nat => vz_125 | 127%nat => vz_127 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 128%nat. }
  assert (HR: regs_ok E PdrFa.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdrFa.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdrFa.kn0).
  { unfold know_ok, PdrFa.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV22l HV22r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV23l HV23r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV25l HV25r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV26l HV26r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV27l HV27r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K33]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdrFa.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdrFa.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 624) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PdrFa.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdrFa.ps0) with 0x12020c in Hms. change (SR.ps_regs PdrFa.ps0) with (map (fun i => (i, nth i PdrFa.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdrFa.ps0) with PdrFa.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdrFa.regs0 PdrFa.regs_out0 140 KS_drFa KS_drFa_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrFa.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PdrFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV22l HV22r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV24l HV24r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV25l HV25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV26l HV26r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV27l HV27r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdrGa := LibSegBa_drGa_b.
Definition KS_drGa : list nat := Eval vm_compute in (BG.kept_list 140 PdrGa.regs0 PdrGa.regs_out0).
Lemma KS_drGa_ok : BG.kept_ok 140 PdrGa.regs0 PdrGa.regs_out0 KS_drGa = true. Proof. vm_compute. reflexivity. Qed.
Lemma drGa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 20%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 118%nat) < 2 ^ 64 -> 0 <= (V 119%nat) < 2 ^ 64 -> 0 <= (V 120%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 9) = Z_to_bv 64 1293512 -> getr R (reg 18) = Z_to_bv 64 (V 118%nat) -> getr R (reg 19) = Z_to_bv 64 (V 119%nat) -> getr R (reg 20) = Z_to_bv 64 (V 120%nat) -> getr R (reg 21) = Z_to_bv 64 6896960 -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.defined M ((V 2%nat) - 16) 16 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 1 <= (V 34%nat) <= 1 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.writable RSEGS M 1293512 4 -> L5.writable RSEGS M 1293544 8 -> L5.writable RSEGS M 1293552 8 -> L5.writable RSEGS M 1293568 8 ->
  L5.writable RSEGS M 1293600 8 -> L5.writable RSEGS M 1293608 8 -> L5.u64_at RSEGS M 1293600 ((V 2%nat) + 128) -> L5.u64_at RSEGS M 1293608 80 ->
  L5.u64_at RSEGS M 6896960 (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 40) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 104) 1184320 -> L5.u64_at RSEGS M ((V 2%nat) + 96) 1293512 ->
  L5.u64_at RSEGS M ((V 2%nat) + 88) 21 -> L5.u64_at RSEGS M ((V 2%nat) + 80) 6896960 -> L5.u64_at RSEGS M ((V 2%nat) + 72) 1 -> L5.u64_at RSEGS M ((V 2%nat) + 64) 6898968 ->
  L5.u64_at RSEGS M ((V 2%nat) + 56) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 48) (V 22%nat) -> L5.u32_at RSEGS M 1293512 5 -> L5.u64_at RSEGS M ((V 2%nat) + 416) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 472) 426864 -> L5.u64_at RSEGS M ((V 2%nat) + 464) 127251 -> L5.u64_at RSEGS M ((V 2%nat) + 456) 1293512 -> L5.u64_at RSEGS M ((V 2%nat) + 448) ((V 2%nat) + 544) ->
  L5.u64_at RSEGS M ((V 2%nat) + 440) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 432) (V 20%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 424) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 536) 687464 ->
  L5.u64_at RSEGS M ((V 2%nat) + 528) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 520) (V 9%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 512) (V 18%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> ~ (1293512 <= i < 1293512 + 4) -> ~ (1293544 <= i < 1293544 + 8) -> ~ (1293552 <= i < 1293552 + 8) -> ~ (1293568 <= i < 1293568 + 8) -> ~ (1293600 <= i < 1293600 + 8) -> ~ (1293608 <= i < 1293608 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x120264 M) (st fx' R' 0x118878 M')
        /\ (forall x, In x KS_drGa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 687508
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 592)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 9%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 2
        /\ getr R' (reg 11) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 18%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 19%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 20%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 22%nat)
        /\ L5.u32_at RSEGS M' 1293512 5
        /\ L5.u64_at RSEGS M' 1293608 0
        /\ L5.u64_at RSEGS M' 1293600 6898968
        /\ L5.u64_at RSEGS M' 1293568 0
        /\ L5.u64_at RSEGS M' 1293552 0
        /\ L5.u64_at RSEGS M' 1293544 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G18 G19 G20 G21 G22 pvzI16 K1 K2 K3 K4 pvzI17 pvzI18 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV8l; move HV8l before pvzI2; pose proof (proj2 pvzI2) as HV8r; move HV8r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV9l; move HV9l before pvzI3; pose proof (proj2 pvzI3) as HV9r; move HV9r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV18l; move HV18l before pvzI4; pose proof (proj2 pvzI4) as HV18r; move HV18r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV19l; move HV19l before pvzI5; pose proof (proj2 pvzI5) as HV19r; move HV19r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV20l; move HV20l before pvzI6; pose proof (proj2 pvzI6) as HV20r; move HV20r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV21l; move HV21l before pvzI7; pose proof (proj2 pvzI7) as HV21r; move HV21r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV22l; move HV22l before pvzI8; pose proof (proj2 pvzI8) as HV22r; move HV22r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV33l; move HV33l before pvzI9; pose proof (proj2 pvzI9) as HV33r; move HV33r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV34l; move HV34l before pvzI10; pose proof (proj2 pvzI10) as HV34r; move HV34r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV40l; move HV40l before pvzI11; pose proof (proj2 pvzI11) as HV40r; move HV40r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV118l; move HV118l before pvzI12; pose proof (proj2 pvzI12) as HV118r; move HV118r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV119l; move HV119l before pvzI13; pose proof (proj2 pvzI13) as HV119r; move HV119r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV120l; move HV120l before pvzI14; pose proof (proj2 pvzI14) as HV120r; move HV120r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV122l; move HV122l before pvzI15; pose proof (proj2 pvzI15) as HV122r; move HV122r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K5l; move K5l before pvzI17; pose proof (proj2 pvzI17) as K5r; move K5r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K6l; move K6l before pvzI18; pose proof (proj2 pvzI18) as K6r; move K6r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_8 := V 8%nat) in *. set (vz_9 := V 9%nat) in *. set (vz_18 := V 18%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_20 := V 20%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_22 := V 22%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_118 := V 118%nat) in *. set (vz_119 := V 119%nat) in *. set (vz_120 := V 120%nat) in *. set (vz_122 := V 122%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 8%nat => Z_to_bv 64 vz_8 | 9%nat => Z_to_bv 64 vz_9 | 18%nat => Z_to_bv 64 vz_18 | 19%nat => Z_to_bv 64 vz_19 | 20%nat => Z_to_bv 64 vz_20 | 21%nat => Z_to_bv 64 vz_21 | 22%nat => Z_to_bv 64 vz_22 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 40%nat => Z_to_bv 64 vz_40 | 118%nat => Z_to_bv 64 vz_118 | 119%nat => Z_to_bv 64 vz_119 | 120%nat => Z_to_bv 64 vz_120 | 122%nat => Z_to_bv 64 vz_122 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 8%nat => vz_8 | 9%nat => vz_9 | 18%nat => vz_18 | 19%nat => vz_19 | 20%nat => vz_20 | 21%nat => vz_21 | 22%nat => vz_22 | 33%nat => vz_33 | 34%nat => vz_34 | 40%nat => vz_40 | 118%nat => vz_118 | 119%nat => vz_119 | 120%nat => vz_120 | 122%nat => vz_122 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 123%nat. }
  assert (HR: regs_ok E PdrGa.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdrGa.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdrGa.kn0).
  { unfold know_ok, PdrGa.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV22l HV22r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV20l HV20r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV8l HV8r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV9l HV9r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV18l HV18r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K38]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdrGa.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdrGa.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 16) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply Hfr. unfold PdrGa.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn6; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdrGa.ps0) with 0x118878 in Hms. change (SR.ps_regs PdrGa.ps0) with (map (fun i => (i, nth i PdrGa.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdrGa.ps0) with PdrGa.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdrGa.regs0 PdrGa.regs_out0 140 KS_drGa KS_drGa_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdrGa.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PdrGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrGa.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PdrGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrGa.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PdrGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrGa.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PdrGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrGa.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdrGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrGa.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdrGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrGa.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdrGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrGa.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PdrGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrGa.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PdrGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrGa.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdrGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrGa.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdrGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdrGa.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PdrGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdfA := LibSegBa_dfA_b.
Definition KS_dfA : list nat := Eval vm_compute in (BG.kept_list 140 PdfA.regs0 PdfA.regs_out0).
Lemma KS_dfA_ok : BG.kept_ok 140 PdfA.regs0 PdfA.regs_out0 KS_dfA = true. Proof. vm_compute. reflexivity. Qed.
Lemma dfA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 687464 -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 1293512 -> getr R (reg 11) = Z_to_bv 64 108788 -> getr R (reg 12) = Z_to_bv 64 67108864 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 3248) 3248 -> L5.defined M ((V 2%nat) - 3248) 3248 ->
  L5.img_clear M 65536 1282048 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450760) 80 -> L5.u64_at RSEGS M 2147464472 0 -> L5.u64_at RSEGS M 2147464480 0 -> L5.writable RSEGS M 1293512 4 ->
  L5.writable RSEGS M 1293520 8 -> L5.writable RSEGS M 1293528 8 -> L5.writable RSEGS M 1293544 8 -> L5.writable RSEGS M 1293552 8 ->
  L5.writable RSEGS M 1293568 8 -> L5.writable RSEGS M 1293600 8 -> L5.writable RSEGS M 1293608 8 -> L5.writable RSEGS M 1293648 4 ->
  L5.u8_at RSEGS M 1313048 1 -> L5.u8_at RSEGS M 1906620 1 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u64_at RSEGS M 1282896 1184024 ->
  L5.u64_at RSEGS M 6896960 (V 40%nat) -> L5.u32_at RSEGS M 1293652 4294967295 -> L5.u32_at RSEGS M 1293512 5 -> L5.u64_at RSEGS M 1293608 0 ->
  L5.u64_at RSEGS M 1293600 6898968 -> L5.u32_at RSEGS M 1293648 0 -> L5.u32_at RSEGS M 1293656 4294967295 -> L5.u8_at RSEGS M 1313049 1 ->
  L5.u64_at RSEGS M 1283272 1218816 -> L5.u64_at RSEGS M 1293584 1180112 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 3248) <= bv_unsigned a < ((V 2%nat) - 3248) + 3248) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293520 <= bv_unsigned a < 1293520 + 8) -> ~ (1293528 <= bv_unsigned a < 1293528 + 8) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> ~ (1293648 <= bv_unsigned a < 1293648 + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 3248) <= i < ((V 2%nat) - 3248) + 3248) -> ~ (1293512 <= i < 1293512 + 4) -> ~ (1293520 <= i < 1293520 + 8) -> ~ (1293528 <= i < 1293528 + 8) -> ~ (1293544 <= i < 1293544 + 8) -> ~ (1293552 <= i < 1293552 + 8) -> ~ (1293568 <= i < 1293568 + 8) -> ~ (1293600 <= i < 1293600 + 8) -> ~ (1293608 <= i < 1293608 + 8) -> ~ (1293648 <= i < 1293648 + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x633bc M) (st fx' R' 0x12020c M')
        /\ (forall x, In x KS_dfA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1184320
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 592)
        /\ getr R' (reg 5) = Z_to_bv 64 115
        /\ getr R' (reg 6) = Z_to_bv 64 101
        /\ getr R' (reg 7) = Z_to_bv 64 100
        /\ getr R' (reg 8) = Z_to_bv 64 0
        /\ getr R' (reg 9) = Z_to_bv 64 1293512
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 1180112
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 101
        /\ getr R' (reg 16) = Z_to_bv 64 102
        /\ getr R' (reg 17) = Z_to_bv 64 117
        /\ getr R' (reg 18) = Z_to_bv 64 6896960
        /\ getr R' (reg 19) = Z_to_bv 64 1
        /\ getr R' (reg 20) = Z_to_bv 64 6898968
        /\ getr R' (reg 21) = Z_to_bv 64 6896960
        /\ getr R' (reg 28) = Z_to_bv 64 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 552) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 544) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 536) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 528) 6898968
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 520) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 512) 6896960
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 504) 38
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 496) 1293512
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 488) 1184320
        /\ L5.u64_at RSEGS M' 1293552 ((V 2%nat) - 426)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 427) 10
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 428) 100
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 429) 101
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 430) 115
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 431) 117
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 432) 102
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 433) 101
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 434) 114
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 435) 32
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 436) 44
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 437) 115
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 438) 101
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 439) 116
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 440) 121
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 441) 98
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 442) 32
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 443) 52
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 444) 54
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 445) 56
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 446) 56
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 447) 48
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 448) 49
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 449) 55
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 450) 54
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 480) ((V 2%nat) - 40)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 451) 32
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 452) 61
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 453) 62
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 454) 32
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 455) 116
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 456) 117
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 457) 112
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 458) 110
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 459) 105
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 460) 32
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 461) 58
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 462) 105
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 463) 108
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 464) 99
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 592) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 584) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 576) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 568) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 560) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' 1293544 ((V 2%nat) - 384)
        /\ L5.u64_at RSEGS M' 1293528 0
        /\ L5.u64_at RSEGS M' 1293520 0
        /\ L5.u64_at RSEGS M' 1293568 ((V 2%nat) - 464)
        /\ L5.u32_at RSEGS M' 1293648 18446744073709551615
        /\ L5.u64_at RSEGS M' 1293608 80
        /\ L5.u64_at RSEGS M' 1293600 ((V 2%nat) - 464)
        /\ L5.u32_at RSEGS M' 1293512 5
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 472) ((V 2%nat) - 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 2%nat) - 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 1293512
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 108788
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 426864
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 2%nat) - 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 2%nat) - 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) ((V 2%nat) - 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 15)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 14)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 13)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 67108864
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 17)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 16)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 687464
        /\ L5.defined M' ((V 2%nat) - 426) 210
        /\ L5.defined M' ((V 2%nat) - 112) 8).
Proof.
  intros pvzI1 pvzI2 G1 G2 G10 G11 G12 pvzI3 K1 K2 K3 K4 K5 K6 K6b K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PdfA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdfA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdfA.kn0).
  { unfold know_ok, PdfA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6b]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K29]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdfA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdfA.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 3248) <= bv_unsigned a < (vz_2 - 3248) + 3248) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293520 <= bv_unsigned a < 1293520 + 8) -> ~ (1293528 <= bv_unsigned a < 1293528 + 8) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> ~ (1293648 <= bv_unsigned a < 1293648 + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8 Hn9. apply Hfr. unfold PdfA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn6; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn7; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn8; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn9; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8 Hn9. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdfA.ps0) with 0x12020c in Hms. change (SR.ps_regs PdfA.ps0) with (map (fun i => (i, nth i PdfA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdfA.ps0) with PdfA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdfA.regs0 PdfA.regs_out0 140 KS_dfA KS_dfA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 7 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfA.regs_out0 E' R' 28 Hregs) by (clear; lia). cbn [nth PdfA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 16); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 17); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 18); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 19); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 20); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 21); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 22); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 23); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 24); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 25); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 26); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 27); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 28); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 29); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 30); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 31); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 32); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 33); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 34); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 35); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 36); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_u32_cell with (v := 1042314357) (k := 3); [apply Hcells; apply (nth_error_In _ 37); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia | clear; lia | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_u32_cell with (v := 1042314357) (k := 2); [apply Hcells; apply (nth_error_In _ 37); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia | clear; lia | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_u32_cell with (v := 1042314357) (k := 1); [apply Hcells; apply (nth_error_In _ 37); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia | clear; lia | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_u32_cell with (v := 1042314357) (k := 0); [apply Hcells; apply (nth_error_In _ 37); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia | clear; lia | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_u32_cell with (v := 1886284064) (k := 3); [apply Hcells; apply (nth_error_In _ 38); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia | clear; lia | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_u32_cell with (v := 1886284064) (k := 2); [apply Hcells; apply (nth_error_In _ 38); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia | clear; lia | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_u32_cell with (v := 1886284064) (k := 1); [apply Hcells; apply (nth_error_In _ 38); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia | clear; lia | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_u32_cell with (v := 1886284064) (k := 0); [apply Hcells; apply (nth_error_In _ 38); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia | clear; lia | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_u32_cell with (v := 979987555) (k := 3); [apply Hcells; apply (nth_error_In _ 39); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia | clear; lia | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_u32_cell with (v := 979987555) (k := 2); [apply Hcells; apply (nth_error_In _ 39); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia | clear; lia | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_u32_cell with (v := 979987555) (k := 1); [apply Hcells; apply (nth_error_In _ 39); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia | clear; lia | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_u32_cell with (v := 979987555) (k := 0); [apply Hcells; apply (nth_error_In _ 39); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia | clear; lia | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 40); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 41); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 42); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 43); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 44); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 45); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 46); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 47); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 48); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 49); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 50); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 51); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 52); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 53); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 54); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 55); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 56); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 57); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 58); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 59); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 60); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 61); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 62); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 63); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 64); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 65); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 66); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 67); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 68); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 69); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 70); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 71); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 72); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 73); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 74); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 75); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 76); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 77); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 78); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 79); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 80); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 81); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PdfG := LibSegBa_dfG_b.
Definition KS_dfG : list nat := Eval vm_compute in (BG.kept_list 140 PdfG.regs0 PdfG.regs_out0).
Lemma KS_dfG_ok : BG.kept_ok 140 PdfG.regs0 PdfG.regs_out0 KS_dfG = true. Proof. vm_compute. reflexivity. Qed.
Lemma dfG_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 20%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 118%nat) < 2 ^ 64 -> 0 <= (V 119%nat) < 2 ^ 64 -> 0 <= (V 120%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 9) = Z_to_bv 64 1293512 -> getr R (reg 18) = Z_to_bv 64 (V 118%nat) -> getr R (reg 19) = Z_to_bv 64 (V 119%nat) -> getr R (reg 20) = Z_to_bv 64 (V 120%nat) -> getr R (reg 21) = Z_to_bv 64 6896960 -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.defined M ((V 2%nat) - 16) 16 ->
  L5.img_clear M 65536 1282048 -> L5.writable RSEGS M 1293512 4 -> L5.writable RSEGS M 1293544 8 -> L5.writable RSEGS M 1293552 8 ->
  L5.writable RSEGS M 1293568 8 -> L5.writable RSEGS M 1293600 8 -> L5.writable RSEGS M 1293608 8 -> L5.u64_at RSEGS M 1293600 ((V 2%nat) + 128) ->
  L5.u64_at RSEGS M 1293608 80 -> L5.u64_at RSEGS M 6896960 (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 40) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 104) 1184320 ->
  L5.u64_at RSEGS M ((V 2%nat) + 96) 1293512 -> L5.u64_at RSEGS M ((V 2%nat) + 88) 38 -> L5.u64_at RSEGS M ((V 2%nat) + 80) 6896960 -> L5.u64_at RSEGS M ((V 2%nat) + 72) 1 ->
  L5.u64_at RSEGS M ((V 2%nat) + 64) 6898968 -> L5.u64_at RSEGS M ((V 2%nat) + 56) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 48) (V 22%nat) -> L5.u32_at RSEGS M 1293512 5 ->
  L5.u64_at RSEGS M ((V 2%nat) + 416) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 472) 426864 -> L5.u64_at RSEGS M ((V 2%nat) + 464) 108788 -> L5.u64_at RSEGS M ((V 2%nat) + 456) 1293512 ->
  L5.u64_at RSEGS M ((V 2%nat) + 448) ((V 2%nat) + 544) -> L5.u64_at RSEGS M ((V 2%nat) + 440) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 432) (V 20%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 424) (V 21%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 536) 687464 -> L5.u64_at RSEGS M ((V 2%nat) + 528) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 520) (V 9%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 512) (V 18%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> ~ (1293512 <= i < 1293512 + 4) -> ~ (1293544 <= i < 1293544 + 8) -> ~ (1293552 <= i < 1293552 + 8) -> ~ (1293568 <= i < 1293568 + 8) -> ~ (1293600 <= i < 1293600 + 8) -> ~ (1293608 <= i < 1293608 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x120264 M) (st fx' R' 0x118878 M')
        /\ (forall x, In x KS_dfG -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 687508
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 592)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 9%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 2
        /\ getr R' (reg 11) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 18%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 19%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 20%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 21%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 22%nat)
        /\ L5.u32_at RSEGS M' 1293512 5
        /\ L5.u64_at RSEGS M' 1293608 0
        /\ L5.u64_at RSEGS M' 1293600 6898968
        /\ L5.u64_at RSEGS M' 1293568 0
        /\ L5.u64_at RSEGS M' 1293552 0
        /\ L5.u64_at RSEGS M' 1293544 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G18 G19 G20 G21 G22 pvzI14 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV8l; move HV8l before pvzI2; pose proof (proj2 pvzI2) as HV8r; move HV8r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV9l; move HV9l before pvzI3; pose proof (proj2 pvzI3) as HV9r; move HV9r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV18l; move HV18l before pvzI4; pose proof (proj2 pvzI4) as HV18r; move HV18r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV19l; move HV19l before pvzI5; pose proof (proj2 pvzI5) as HV19r; move HV19r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV20l; move HV20l before pvzI6; pose proof (proj2 pvzI6) as HV20r; move HV20r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV21l; move HV21l before pvzI7; pose proof (proj2 pvzI7) as HV21r; move HV21r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV22l; move HV22l before pvzI8; pose proof (proj2 pvzI8) as HV22r; move HV22r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV40l; move HV40l before pvzI9; pose proof (proj2 pvzI9) as HV40r; move HV40r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV118l; move HV118l before pvzI10; pose proof (proj2 pvzI10) as HV118r; move HV118r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV119l; move HV119l before pvzI11; pose proof (proj2 pvzI11) as HV119r; move HV119r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV120l; move HV120l before pvzI12; pose proof (proj2 pvzI12) as HV120r; move HV120r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV122l; move HV122l before pvzI13; pose proof (proj2 pvzI13) as HV122r; move HV122r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K0l; move K0l before pvzI14; pose proof (proj2 pvzI14) as K0r; move K0r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_8 := V 8%nat) in *. set (vz_9 := V 9%nat) in *. set (vz_18 := V 18%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_20 := V 20%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_22 := V 22%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_118 := V 118%nat) in *. set (vz_119 := V 119%nat) in *. set (vz_120 := V 120%nat) in *. set (vz_122 := V 122%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 8%nat => Z_to_bv 64 vz_8 | 9%nat => Z_to_bv 64 vz_9 | 18%nat => Z_to_bv 64 vz_18 | 19%nat => Z_to_bv 64 vz_19 | 20%nat => Z_to_bv 64 vz_20 | 21%nat => Z_to_bv 64 vz_21 | 22%nat => Z_to_bv 64 vz_22 | 40%nat => Z_to_bv 64 vz_40 | 118%nat => Z_to_bv 64 vz_118 | 119%nat => Z_to_bv 64 vz_119 | 120%nat => Z_to_bv 64 vz_120 | 122%nat => Z_to_bv 64 vz_122 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 8%nat => vz_8 | 9%nat => vz_9 | 18%nat => vz_18 | 19%nat => vz_19 | 20%nat => vz_20 | 21%nat => vz_21 | 22%nat => vz_22 | 40%nat => vz_40 | 118%nat => vz_118 | 119%nat => vz_119 | 120%nat => vz_120 | 122%nat => vz_122 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 123%nat. }
  assert (HR: regs_ok E PdfG.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdfG.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdfG.kn0).
  { unfold know_ok, PdfG.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV22l HV22r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV20l HV20r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV8l HV8r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV9l HV9r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV18l HV18r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K35]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PdfG.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PdfG.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 16) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply Hfr. unfold PdfG.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn6; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdfG.ps0) with 0x118878 in Hms. change (SR.ps_regs PdfG.ps0) with (map (fun i => (i, nth i PdfG.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdfG.ps0) with PdfG.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdfG.regs0 PdfG.regs_out0 140 KS_dfG KS_dfG_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdfG.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PdfG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfG.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PdfG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfG.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PdfG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfG.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PdfG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfG.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PdfG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfG.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdfG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfG.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdfG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfG.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PdfG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfG.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PdfG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfG.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PdfG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfG.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PdfG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdfG.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PdfG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End AS0DIAGRP.
