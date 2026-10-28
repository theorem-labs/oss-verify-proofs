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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_duA_b LibSegBa_duB_b LibSegBa_duD_b LibSegBa_duDs_b LibSegBa_duDl_b LibSegBa_duEa_b LibSegBa_duEb_b LibSegBa_duFa_b LibSegBa_duGa_b LibSegBa_duGb1_b LibSegBa_duGb2_b LibSegBa_duEc_b LibSegBa_duGc_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module AS0DIAGUP.
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
Module PduA := LibSegBa_duA_b.
Definition KS_duA : list nat := Eval vm_compute in (BG.kept_list 140 PduA.regs0 PduA.regs_out0).
Lemma KS_duA_ok : BG.kept_ok 140 PduA.regs0 PduA.regs_out0 KS_duA = true. Proof. vm_compute. reflexivity. Qed.
Lemma duA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 687288 -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 1293512 -> getr R (reg 11) = Z_to_bv 64 90394 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 2352) 2352 -> L5.defined M ((V 2%nat) - 2352) 2352 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 131071 -> (((V 2%nat) - 2352) + 2352 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 2352)) ->
  L5.u64_at RSEGS M 2147462176 0 -> L5.u8_at RSEGS M 1313048 1 -> L5.u8_at RSEGS M 1906620 1 -> L5.u64_at RSEGS M 1309752 2147450880 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 2352) <= bv_unsigned a < ((V 2%nat) - 2352) + 2352) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 2352) <= i < ((V 2%nat) - 2352) + 2352) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x633bc M) (st fx' R' 0x674b0 M')
        /\ (forall x, In x KS_duA -> getr R' (reg x) = getr R (reg x))
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
        /\ getr R' (reg 19) = Z_to_bv 64 90403
        /\ getr R' (reg 20) = Z_to_bv 64 88935
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 40)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 9
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 2%nat) - 2296)
        /\ getr R' (reg 25) = Z_to_bv 64 12297829382473034410
        /\ getr R' (reg 26) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 27) = Z_to_bv 64 37
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2292) 115
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2304) 90403
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2296) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2312) 90401
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 90394
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 687288
        /\ L5.defined M' ((V 2%nat) - 2352) 8
        /\ L5.defined M' ((V 2%nat) - 2288) 2072
        /\ L5.defined M' ((V 2%nat) - 112) 8).
Proof.
  intros pvzI1 pvzI2 pvzI3 G1 G2 G10 G11 G12 pvzI4 K1 K2 K3 K4 pvzI5 pvzI6 K7 K8 K9 K10 K11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K5l; move K5l before pvzI5; pose proof (proj2 pvzI5) as K5r; move K5r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PduA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduA.kn0).
  { unfold know_ok, PduA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K11]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PduA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PduA.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 2352) <= bv_unsigned a < (vz_2 - 2352) + 2352) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PduA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduA.ps0) with 0x674b0 in Hms. change (SR.ps_regs PduA.ps0) with (map (fun i => (i, nth i PduA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduA.ps0) with PduA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduA.regs0 PduA.regs_out0 140 KS_duA KS_duA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
Module PduB := LibSegBa_duB_b.
Definition KS_duB : list nat := Eval vm_compute in (BG.kept_list 140 PduB.regs0 PduB.regs_out0).
Lemma KS_duB_ok : BG.kept_ok 140 PduB.regs0 PduB.regs_out0 KS_duB = true. Proof. vm_compute. reflexivity. Qed.
Lemma duB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 20%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 23%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 25%nat) < 2 ^ 64 -> 0 <= (V 26%nat) < 2 ^ 64 -> 0 <= (V 27%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 120%nat) < 2 ^ 64 -> 0 <= (V 121%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 -> 0 <= (V 123%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) + 2240) -> getr R (reg 19) = Z_to_bv 64 90403 -> getr R (reg 20) = Z_to_bv 64 (V 120%nat) -> getr R (reg 21) = Z_to_bv 64 (V 121%nat) -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) -> getr R (reg 23) = Z_to_bv 64 (V 123%nat) -> getr R (reg 24) = Z_to_bv 64 ((V 2%nat) + 56) -> getr R (reg 25) = Z_to_bv 64 12297829382473034410 -> getr R (reg 26) = Z_to_bv 64 18446744073709551615 -> getr R (reg 27) = Z_to_bv 64 37 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 896) 3136 -> L5.defined M ((V 2%nat) - 896) 3136 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 131071 -> (((V 2%nat) - 896) + 3136 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 896)) ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147451102) 24 -> L5.u64_at RSEGS M 2147462176 0 -> L5.writable RSEGS M 1293512 4 -> L5.writable RSEGS M 1293520 8 ->
  L5.writable RSEGS M 1293528 8 -> L5.writable RSEGS M 1293544 8 -> L5.writable RSEGS M 1293552 8 -> L5.writable RSEGS M 1293568 8 ->
  L5.writable RSEGS M 1293600 8 -> L5.writable RSEGS M 1293608 8 -> L5.writable RSEGS M 1293648 4 -> L5.u64_at RSEGS M ((V 2%nat) + 2232) 426800 ->
  L5.u64_at RSEGS M ((V 2%nat) + 2224) 90394 -> L5.u64_at RSEGS M ((V 2%nat) + 2216) 1293512 -> L5.u64_at RSEGS M ((V 2%nat) + 2208) ((V 2%nat) + 2304) -> L5.u64_at RSEGS M ((V 2%nat) + 2200) (V 19%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 2192) (V 20%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2184) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2176) (V 22%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2168) (V 23%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 2160) (V 24%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2152) (V 25%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2144) (V 26%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2136) (V 27%nat) ->
  L5.u64_at RSEGS M 1282896 1184024 -> L5.u64_at RSEGS M ((V 2%nat) + 2264) ((V 2%nat) + 2304) -> L5.u64_at RSEGS M 6896960 (V 40%nat) -> L5.u32_at RSEGS M 1293652 4294967295 ->
  L5.u32_at RSEGS M 1293512 5 -> L5.u64_at RSEGS M 1293608 0 -> L5.u64_at RSEGS M 1293600 6898968 -> L5.u32_at RSEGS M 1293648 0 ->
  L5.u32_at RSEGS M 1293656 4294967295 -> L5.u8_at RSEGS M 1313049 1 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u64_at RSEGS M 1283272 1218816 ->
  L5.u64_at RSEGS M ((V 2%nat) + 2304) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 896) <= bv_unsigned a < ((V 2%nat) - 896) + 3136) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293520 <= bv_unsigned a < 1293520 + 8) -> ~ (1293528 <= bv_unsigned a < 1293528 + 8) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> ~ (1293648 <= bv_unsigned a < 1293648 + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 896) <= i < ((V 2%nat) - 896) + 3136) -> ~ (1293512 <= i < 1293512 + 4) -> ~ (1293520 <= i < 1293520 + 8) -> ~ (1293528 <= i < 1293528 + 8) -> ~ (1293544 <= i < 1293544 + 8) -> ~ (1293552 <= i < 1293552 + 8) -> ~ (1293568 <= i < 1293568 + 8) -> ~ (1293600 <= i < 1293600 + 8) -> ~ (1293608 <= i < 1293608 + 8) -> ~ (1293648 <= i < 1293648 + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x67414 M) (st fx' R' 0x63370 M')
        /\ (forall x, In x KS_duB -> getr R' (reg x) = getr R (reg x))
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
        /\ getr R' (reg 18) = Z_to_bv 64 2147483640
        /\ getr R' (reg 19) = Z_to_bv 64 7
        /\ getr R' (reg 20) = Z_to_bv 64 1293512
        /\ getr R' (reg 21) = Z_to_bv 64 90403
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 26) = Z_to_bv 64 0
        /\ getr R' (reg 27) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1440) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1872) ((V 2%nat) + 2312)
        /\ L5.u64_at RSEGS M' 1293552 ((V 2%nat) + 1895)
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1894) 32
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1893) 58
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1892) 101
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1891) 103
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1890) 97
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1889) 115
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1888) 117
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1848) 90394
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2224) 90394
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2232) 426864
        /\ L5.defined M' ((V 2%nat) + 1328) 40
        /\ L5.defined M' ((V 2%nat) + 1448) 312
        /\ L5.defined M' ((V 2%nat) + 1895) 241).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI18 K1 K2 K3 K4 pvzI19 pvzI20 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV19l; move HV19l before pvzI2; pose proof (proj2 pvzI2) as HV19r; move HV19r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV20l; move HV20l before pvzI3; pose proof (proj2 pvzI3) as HV20r; move HV20r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV21l; move HV21l before pvzI4; pose proof (proj2 pvzI4) as HV21r; move HV21r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV22l; move HV22l before pvzI5; pose proof (proj2 pvzI5) as HV22r; move HV22r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV23l; move HV23l before pvzI6; pose proof (proj2 pvzI6) as HV23r; move HV23r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV24l; move HV24l before pvzI7; pose proof (proj2 pvzI7) as HV24r; move HV24r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV25l; move HV25l before pvzI8; pose proof (proj2 pvzI8) as HV25r; move HV25r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV26l; move HV26l before pvzI9; pose proof (proj2 pvzI9) as HV26r; move HV26r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV27l; move HV27l before pvzI10; pose proof (proj2 pvzI10) as HV27r; move HV27r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV33l; move HV33l before pvzI11; pose proof (proj2 pvzI11) as HV33r; move HV33r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV34l; move HV34l before pvzI12; pose proof (proj2 pvzI12) as HV34r; move HV34r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV40l; move HV40l before pvzI13; pose proof (proj2 pvzI13) as HV40r; move HV40r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV120l; move HV120l before pvzI14; pose proof (proj2 pvzI14) as HV120r; move HV120r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV121l; move HV121l before pvzI15; pose proof (proj2 pvzI15) as HV121r; move HV121r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV122l; move HV122l before pvzI16; pose proof (proj2 pvzI16) as HV122r; move HV122r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV123l; move HV123l before pvzI17; pose proof (proj2 pvzI17) as HV123r; move HV123r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K5l; move K5l before pvzI19; pose proof (proj2 pvzI19) as K5r; move K5r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K6l; move K6l before pvzI20; pose proof (proj2 pvzI20) as K6r; move K6r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_20 := V 20%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_22 := V 22%nat) in *. set (vz_23 := V 23%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_25 := V 25%nat) in *. set (vz_26 := V 26%nat) in *. set (vz_27 := V 27%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_120 := V 120%nat) in *. set (vz_121 := V 121%nat) in *. set (vz_122 := V 122%nat) in *. set (vz_123 := V 123%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 19%nat => Z_to_bv 64 vz_19 | 20%nat => Z_to_bv 64 vz_20 | 21%nat => Z_to_bv 64 vz_21 | 22%nat => Z_to_bv 64 vz_22 | 23%nat => Z_to_bv 64 vz_23 | 24%nat => Z_to_bv 64 vz_24 | 25%nat => Z_to_bv 64 vz_25 | 26%nat => Z_to_bv 64 vz_26 | 27%nat => Z_to_bv 64 vz_27 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 40%nat => Z_to_bv 64 vz_40 | 120%nat => Z_to_bv 64 vz_120 | 121%nat => Z_to_bv 64 vz_121 | 122%nat => Z_to_bv 64 vz_122 | 123%nat => Z_to_bv 64 vz_123 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 19%nat => vz_19 | 20%nat => vz_20 | 21%nat => vz_21 | 22%nat => vz_22 | 23%nat => vz_23 | 24%nat => vz_24 | 25%nat => vz_25 | 26%nat => vz_26 | 27%nat => vz_27 | 33%nat => vz_33 | 34%nat => vz_34 | 40%nat => vz_40 | 120%nat => vz_120 | 121%nat => vz_121 | 122%nat => vz_122 | 123%nat => vz_123 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 124%nat. }
  assert (HR: regs_ok E PduB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduB.kn0).
  { unfold know_ok, PduB.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV20l HV20r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV22l HV22r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV23l HV23r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV25l HV25r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV26l HV26r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV27l HV27r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K44]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PduB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PduB.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 896) <= bv_unsigned a < (vz_2 - 896) + 3136) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293520 <= bv_unsigned a < 1293520 + 8) -> ~ (1293528 <= bv_unsigned a < 1293528 + 8) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> ~ (1293648 <= bv_unsigned a < 1293648 + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8 Hn9. apply Hfr. unfold PduB.F0.
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
  change (SR.ps_pc PduB.ps0) with 0x63370 in Hms. change (SR.ps_regs PduB.ps0) with (map (fun i => (i, nth i PduB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduB.ps0) with PduB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduB.regs0 PduB.regs_out0 140 KS_duB KS_duB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV27l HV27r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV26l HV26r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV25l HV25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV24l HV24r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV23l HV23r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV22l HV22r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 29); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 30); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 31); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 32); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 34); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 35); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 36); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 37); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 38); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 39); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 40); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 41); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 42); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 43); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 44); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 45); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 46); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 47); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 48); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV21l HV21r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 49); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV20l HV20r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 50); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 51); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 52); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 53); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 54); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 55); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 56); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 57); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduD := LibSegBa_duD_b.
Definition KS_duD : list nat := Eval vm_compute in (BG.kept_list 140 PduD.regs0 PduD.regs_out0).
Lemma KS_duD_ok : BG.kept_ok 140 PduD.regs0 PduD.regs_out0 KS_duD = true. Proof. vm_compute. reflexivity. Qed.
Lemma duD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 37 -> getr R (reg 9) = Z_to_bv 64 2147483647 -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 2147483640 -> getr R (reg 19) = Z_to_bv 64 7 -> getr R (reg 20) = Z_to_bv 64 1293512 -> getr R (reg 21) = Z_to_bv 64 90403 -> getr R (reg 22) = Z_to_bv 64 0 -> getr R (reg 23) = Z_to_bv 64 (V 33%nat) -> getr R (reg 25) = Z_to_bv 64 18446744073709551615 -> getr R (reg 26) = Z_to_bv 64 0 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 2224) 2272 -> L5.defined M ((V 2%nat) - 2224) 2272 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 131071 -> (((V 2%nat) - 2224) + 2272 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 2224)) ->
  L5.writable RSEGS M 1293552 8 -> L5.u8_at RSEGS M 1293512 5 -> L5.u64_at RSEGS M 1293544 ((V 2%nat) + 640) -> L5.u64_at RSEGS M 1293552 ((V 2%nat) + 567) ->
  L5.u32_at RSEGS M 1293656 4294967295 -> L5.u8_at RSEGS M 1313049 1 -> L5.u64_at RSEGS M 1283272 1218816 -> L5.u8_at RSEGS M ((V 33%nat) + (V 34%nat)) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 2224) <= bv_unsigned a < ((V 2%nat) - 2224) + 2272) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 2224) <= i < ((V 2%nat) - 2224) + 2272) -> ~ (1293552 <= i < 1293552 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x1218e0 M) (st fx' R' 0x121e2c M')
        /\ (forall x, In x KS_duD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1187080
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 1293512
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) + 567)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 3
        /\ getr R' (reg 18) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' 1293552 ((V 2%nat) + 567)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 32) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 16) (V 34%nat)
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
  assert (HR: regs_ok E PduD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduD.kn0).
  { unfold know_ok, PduD.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7 HV34l HV34r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K5l K5r K7 HV34l HV34r K6l K6r; lia | clear - HV33l HV33r K5l K5r K7 HV34l HV34r K6l K6r; lia | byte_tac ltac:(clear) | exactA K15]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PduD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PduD.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 2224) <= bv_unsigned a < (vz_2 - 2224) + 2272) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PduD.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduD.ps0) with 0x121e2c in Hms. change (SR.ps_regs PduD.ps0) with (map (fun i => (i, nth i PduD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduD.ps0) with PduD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduD.regs0 PduD.regs_out0 140 KS_duD KS_duD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduDs := LibSegBa_duDs_b.
Definition KS_duDs : list nat := Eval vm_compute in (BG.kept_list 140 PduDs.regs0 PduDs.regs_out0).
Lemma KS_duDs_ok : BG.kept_ok 140 PduDs.regs0 PduDs.regs_out0 KS_duDs = true. Proof. vm_compute. reflexivity. Qed.
Lemma duDs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 37 -> getr R (reg 9) = Z_to_bv 64 2147483647 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 1293512 -> getr R (reg 18) = Z_to_bv 64 0 -> getr R (reg 19) = Z_to_bv 64 7 -> getr R (reg 20) = Z_to_bv 64 1293512 -> getr R (reg 21) = Z_to_bv 64 90403 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.defined M ((V 2%nat) - 64) 64 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 73 -> (((V 2%nat) - 64) + 64 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 64)) ->
  L5.u64_at RSEGS M 1293544 ((V 2%nat) + 640) -> L5.u64_at RSEGS M 1293552 ((V 2%nat) + 567) -> L5.u32_at RSEGS M 1293656 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x121e2c M) (st fx' R' 0x77c90 M')
        /\ (forall x, In x KS_duDs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1182924
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 1293512
        /\ getr R' (reg 9) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) + 567)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 90403
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 1293512
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 7
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
  assert (HR: regs_ok E PduDs.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduDs.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduDs.kn0).
  { unfold know_ok, PduDs.kn0.
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
  pvz_hg ltac:(idtac; destruct (PduDs.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PduDs.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 64) <= bv_unsigned a < (vz_2 - 64) + 64) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PduDs.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduDs.ps0) with 0x77c90 in Hms. change (SR.ps_regs PduDs.ps0) with (map (fun i => (i, nth i PduDs.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduDs.ps0) with PduDs.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduDs.regs0 PduDs.regs_out0 140 KS_duDs KS_duDs_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
Module PduDl := LibSegBa_duDl_b.
Definition KS_duDl : list nat := Eval vm_compute in (BG.kept_list 140 PduDl.regs0 PduDl.regs_out0).
Lemma KS_duDl_ok : BG.kept_ok 140 PduDl.regs0 PduDl.regs_out0 KS_duDl = true. Proof. vm_compute. reflexivity. Qed.
Lemma duDl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 37 -> getr R (reg 9) = Z_to_bv 64 2147483647 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 1293512 -> getr R (reg 18) = Z_to_bv 64 0 -> getr R (reg 19) = Z_to_bv 64 7 -> getr R (reg 20) = Z_to_bv 64 1293512 -> getr R (reg 21) = Z_to_bv 64 90403 -> getr R (reg 22) = Z_to_bv 64 0 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> L5.defined M ((V 2%nat) - 112) 112 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 74 <= (V 34%nat) <= 131071 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 112)) ->
  L5.u64_at RSEGS M 1293544 ((V 2%nat) + 640) -> L5.u64_at RSEGS M 1293552 ((V 2%nat) + 567) -> L5.u64_at RSEGS M 1293584 1180112 -> L5.u64_at RSEGS M 6896960 (V 40%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 112) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 112) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x121e2c M) (st fx' R' 0x12020c M')
        /\ (forall x, In x KS_duDl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1187376
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 6) = Z_to_bv 64 1180112
        /\ getr R' (reg 8) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 1293512
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 6896960
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 90403
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 1293512
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 7
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) 2147483647
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) 37
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) 1187376
        /\ L5.defined M' ((V 2%nat) - 112) 40).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 pvzI5 K1 K2 K3 K4 pvzI6 pvzI7 K7 K8 K9 K10 K11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K5l; move K5l before pvzI6; pose proof (proj2 pvzI6) as K5r; move K5r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PduDl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduDl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduDl.kn0).
  { unfold know_ok, PduDl.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K11]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PduDl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PduDl.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 112) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PduDl.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduDl.ps0) with 0x12020c in Hms. change (SR.ps_regs PduDl.ps0) with (map (fun i => (i, nth i PduDl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduDl.ps0) with PduDl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduDl.regs0 PduDl.regs_out0 140 KS_duDl KS_duDl_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduEa := LibSegBa_duEa_b.
Definition KS_duEa : list nat := Eval vm_compute in (BG.kept_list 140 PduEa.regs0 PduEa.regs_out0).
Lemma KS_duEa_ok : BG.kept_ok 140 PduEa.regs0 PduEa.regs_out0 KS_duEa = true. Proof. vm_compute. reflexivity. Qed.
Lemma duEa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 1293512 -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 0 -> getr R (reg 26) = Z_to_bv 64 (V 34%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 80 -> L5.defined M ((V 2%nat) - 16) 80 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 66 -> (((V 2%nat) - 16) + 80 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.writable RSEGS M 1293552 8 -> L5.u64_at RSEGS M 1293552 ((V 2%nat) + 631) -> L5.u64_at RSEGS M ((V 2%nat) + 56) 1187376 -> L5.u64_at RSEGS M ((V 2%nat) + 48) 37 ->
  L5.u64_at RSEGS M ((V 2%nat) + 40) 2147483647 -> L5.u64_at RSEGS M ((V 2%nat) + 32) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 24) 7 -> L5.u64_at RSEGS M ((V 2%nat) + 16) 1293512 ->
  L5.u64_at RSEGS M ((V 2%nat) + 8) 90403 -> L5.u8_at RSEGS M 1293512 5 -> L5.u64_at RSEGS M 1293544 ((V 2%nat) + 704) -> L5.u32_at RSEGS M 1293656 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 80) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 80) -> ~ (1293552 <= i < 1293552 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x120ccc M) (st fx' R' 0x77c90 M')
        /\ (forall x, In x KS_duEa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1182924
        /\ getr R' (reg 9) = Z_to_bv 64 7
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 2%nat) + (V 34%nat)) + 631)
        /\ getr R' (reg 11) = Z_to_bv 64 90403
        /\ getr R' (reg 12) = Z_to_bv 64 7
        /\ getr R' (reg 18) = Z_to_bv 64 90403
        /\ getr R' (reg 20) = Z_to_bv 64 1293512
        /\ getr R' (reg 21) = Z_to_bv 64 90410
        /\ getr R' (reg 22) = Z_to_bv 64 7
        /\ getr R' (reg 23) = Z_to_bv 64 90403
        /\ getr R' (reg 26) = Z_to_bv 64 7
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) 90410
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 16) 1293512
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 24) ((V 34%nat) + 7)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 32) (((-1) * (V 34%nat)) + 2147483640)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 40) 2147483647
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 48) 37
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 56) 1184784
        /\ L5.u64_at RSEGS M' 1293552 (((V 2%nat) + (V 34%nat)) + 631)).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G9 G19 G26 pvzI4 K1 K2 K3 K4 pvzI5 pvzI6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K5l; move K5l before pvzI5; pose proof (proj2 pvzI5) as K5r; move K5r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PduEa.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduEa.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduEa.kn0).
  { unfold know_ok, PduEa.kn0.
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
  pvz_hg ltac:(idtac; destruct (PduEa.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PduEa.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 80) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PduEa.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduEa.ps0) with 0x77c90 in Hms. change (SR.ps_regs PduEa.ps0) with (map (fun i => (i, nth i PduEa.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduEa.ps0) with PduEa.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduEa.regs0 PduEa.regs_out0 140 KS_duEa KS_duEa_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 HV34l HV34r K6l K6r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduEb := LibSegBa_duEb_b.
Definition KS_duEb : list nat := Eval vm_compute in (BG.kept_list 140 PduEb.regs0 PduEb.regs_out0).
Lemma KS_duEb_ok : BG.kept_ok 140 PduEb.regs0 PduEb.regs_out0 KS_duEb = true. Proof. vm_compute. reflexivity. Qed.
Lemma duEb_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 1293512 -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 0 -> getr R (reg 26) = Z_to_bv 64 (V 34%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 112 -> L5.defined M ((V 2%nat) - 48) 112 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 67 <= (V 34%nat) <= 73 -> (((V 2%nat) - 48) + 112 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 48)) ->
  L5.writable RSEGS M 1293552 8 -> L5.u64_at RSEGS M 1293552 ((V 2%nat) + 631) -> L5.u64_at RSEGS M ((V 2%nat) + 56) 1187376 -> L5.u64_at RSEGS M ((V 2%nat) + 48) 37 ->
  L5.u64_at RSEGS M ((V 2%nat) + 40) 2147483647 -> L5.u64_at RSEGS M ((V 2%nat) + 32) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 24) 7 -> L5.u64_at RSEGS M ((V 2%nat) + 16) 1293512 ->
  L5.u64_at RSEGS M ((V 2%nat) + 8) 90403 -> L5.u8_at RSEGS M 1293512 5 -> L5.u64_at RSEGS M 1293544 ((V 2%nat) + 704) -> L5.u64_at RSEGS M 1293584 1180112 ->
  L5.u64_at RSEGS M 6896960 (V 40%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 112) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 112) -> ~ (1293552 <= i < 1293552 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x120ccc M) (st fx' R' 0x12020c M')
        /\ (forall x, In x KS_duEb -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1184784
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 6) = Z_to_bv 64 1180112
        /\ getr R' (reg 8) = Z_to_bv 64 7
        /\ getr R' (reg 9) = Z_to_bv 64 1293512
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 90403
        /\ getr R' (reg 12) = Z_to_bv 64 7
        /\ getr R' (reg 18) = Z_to_bv 64 (((-1) * (V 34%nat)) + 2147483640)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 34%nat) + 7)
        /\ getr R' (reg 20) = Z_to_bv 64 1293512
        /\ getr R' (reg 21) = Z_to_bv 64 6896960
        /\ getr R' (reg 22) = Z_to_bv 64 7
        /\ getr R' (reg 23) = Z_to_bv 64 90403
        /\ getr R' (reg 26) = Z_to_bv 64 7
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' (V 2%nat) 7
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) 90410
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 16) 1293512
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 24) ((V 34%nat) + 7)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 32) (((-1) * (V 34%nat)) + 2147483640)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 40) 2147483647
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 48) 37
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 56) 1184784
        /\ L5.u64_at RSEGS M' 1293552 (((V 2%nat) + (V 34%nat)) + 631)
        /\ L5.defined M' ((V 2%nat) - 48) 40).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G19 G26 pvzI5 K1 K2 K3 K4 pvzI6 pvzI7 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K5l; move K5l before pvzI6; pose proof (proj2 pvzI6) as K5r; move K5r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PduEb.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduEb.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduEb.kn0).
  { unfold know_ok, PduEb.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K20]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PduEb.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PduEb.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 112) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PduEb.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduEb.ps0) with 0x12020c in Hms. change (SR.ps_regs PduEb.ps0) with (map (fun i => (i, nth i PduEb.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduEb.ps0) with PduEb.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduEb.regs0 PduEb.regs_out0 140 KS_duEb KS_duEb_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 HV34l HV34r K6l K6r) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduFa := LibSegBa_duFa_b.
Definition KS_duFa : list nat := Eval vm_compute in (BG.kept_list 140 PduFa.regs0 PduFa.regs_out0).
Lemma KS_duFa_ok : BG.kept_ok 140 PduFa.regs0 PduFa.regs_out0 KS_duFa = true. Proof. vm_compute. reflexivity. Qed.
Lemma duFa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 23%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 25%nat) < 2 ^ 64 -> 0 <= (V 26%nat) < 2 ^ 64 -> 0 <= (V 27%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 123%nat) < 2 ^ 64 -> 0 <= (V 124%nat) < 2 ^ 64 -> 0 <= (V 125%nat) < 2 ^ 64 -> 0 <= (V 127%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 1293512 -> getr R (reg 9) = Z_to_bv 64 7 -> getr R (reg 19) = Z_to_bv 64 0 -> getr R (reg 22) = Z_to_bv 64 7 -> getr R (reg 23) = Z_to_bv 64 (V 123%nat) -> getr R (reg 24) = Z_to_bv 64 (V 124%nat) -> getr R (reg 25) = Z_to_bv 64 (V 125%nat) -> getr R (reg 26) = Z_to_bv 64 7 -> getr R (reg 27) = Z_to_bv 64 (V 127%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 624 -> L5.defined M ((V 2%nat) - 16) 624 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 66 -> (((V 2%nat) - 16) + 624 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.writable RSEGS M 1293552 8 -> L5.u64_at RSEGS M 1293552 (((V 2%nat) + (V 34%nat)) + 631) -> L5.u64_at RSEGS M ((V 2%nat) + 56) 1184784 -> L5.u64_at RSEGS M ((V 2%nat) + 48) 37 ->
  L5.u64_at RSEGS M ((V 2%nat) + 40) 2147483647 -> L5.u64_at RSEGS M ((V 2%nat) + 32) (2147483640 - (V 34%nat)) -> L5.u64_at RSEGS M ((V 2%nat) + 24) ((V 34%nat) + 7) -> L5.u64_at RSEGS M ((V 2%nat) + 16) 1293512 ->
  L5.u64_at RSEGS M ((V 2%nat) + 8) 90410 -> L5.u64_at RSEGS M ((V 2%nat) + 160) 6896960 -> L5.u64_at RSEGS M 6896960 (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 496) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 600) 1184288 -> L5.u64_at RSEGS M ((V 2%nat) + 592) 1293512 -> L5.u64_at RSEGS M ((V 2%nat) + 584) 90394 -> L5.u64_at RSEGS M ((V 2%nat) + 576) 6896960 ->
  L5.u64_at RSEGS M ((V 2%nat) + 568) 1 -> L5.u64_at RSEGS M ((V 2%nat) + 560) 6898968 -> L5.u64_at RSEGS M ((V 2%nat) + 552) 5 -> L5.u64_at RSEGS M ((V 2%nat) + 544) (V 22%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 536) (V 23%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 528) (V 24%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 520) (V 25%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 512) (V 26%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 504) (V 27%nat) -> L5.u64_at RSEGS M 1293584 1180112 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 624) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 624) -> ~ (1293552 <= i < 1293552 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x120ccc M) (st fx' R' 0x12020c M')
        /\ (forall x, In x KS_duFa -> getr R' (reg x) = getr R (reg x))
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 584) ((V 34%nat) + 14)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 592) 1293512
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 600) 1184320
        /\ L5.u64_at RSEGS M' 1293552 (((V 2%nat) + (V 34%nat)) + 638)
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
  assert (HR: regs_ok E PduFa.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduFa.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduFa.kn0).
  { unfold know_ok, PduFa.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 HV34l HV34r K6l K6r) | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K14]. }
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
  pvz_hg ltac:(idtac; destruct (PduFa.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PduFa.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 624) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PduFa.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduFa.ps0) with 0x12020c in Hms. change (SR.ps_regs PduFa.ps0) with (map (fun i => (i, nth i PduFa.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduFa.ps0) with PduFa.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduFa.regs0 PduFa.regs_out0 140 KS_duFa KS_duFa_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV22l HV22r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 HV34l HV34r K6l K6r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV24l HV24r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV25l HV25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV26l HV26r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV27l HV27r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduGa := LibSegBa_duGa_b.
Definition KS_duGa : list nat := Eval vm_compute in (BG.kept_list 140 PduGa.regs0 PduGa.regs_out0).
Lemma KS_duGa_ok : BG.kept_ok 140 PduGa.regs0 PduGa.regs_out0 KS_duGa = true. Proof. vm_compute. reflexivity. Qed.
Lemma duGa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 20%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 118%nat) < 2 ^ 64 -> 0 <= (V 119%nat) < 2 ^ 64 -> 0 <= (V 120%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 9) = Z_to_bv 64 1293512 -> getr R (reg 18) = Z_to_bv 64 (V 118%nat) -> getr R (reg 19) = Z_to_bv 64 (V 119%nat) -> getr R (reg 20) = Z_to_bv 64 (V 120%nat) -> getr R (reg 21) = Z_to_bv 64 6896960 -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.defined M ((V 2%nat) - 16) 16 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 66 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.writable RSEGS M 1293512 4 -> L5.writable RSEGS M 1293544 8 -> L5.writable RSEGS M 1293552 8 -> L5.writable RSEGS M 1293568 8 ->
  L5.writable RSEGS M 1293600 8 -> L5.writable RSEGS M 1293608 8 -> L5.u64_at RSEGS M 1293600 ((V 2%nat) + 128) -> L5.u64_at RSEGS M 1293608 80 ->
  L5.u64_at RSEGS M 6896960 (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 40) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 104) 1184320 -> L5.u64_at RSEGS M ((V 2%nat) + 96) 1293512 ->
  L5.u64_at RSEGS M ((V 2%nat) + 88) ((V 34%nat) + 14) -> L5.u64_at RSEGS M ((V 2%nat) + 80) 6896960 -> L5.u64_at RSEGS M ((V 2%nat) + 72) 1 -> L5.u64_at RSEGS M ((V 2%nat) + 64) 6898968 ->
  L5.u64_at RSEGS M ((V 2%nat) + 56) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 48) (V 22%nat) -> L5.u32_at RSEGS M 1293512 5 -> L5.u64_at RSEGS M ((V 2%nat) + 416) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 472) 426864 -> L5.u64_at RSEGS M ((V 2%nat) + 464) 90394 -> L5.u64_at RSEGS M ((V 2%nat) + 456) 1293512 -> L5.u64_at RSEGS M ((V 2%nat) + 448) ((V 2%nat) + 544) ->
  L5.u64_at RSEGS M ((V 2%nat) + 440) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 432) (V 20%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 424) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 536) 687288 ->
  L5.u64_at RSEGS M ((V 2%nat) + 528) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 520) (V 9%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 512) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 664) 1147056 ->
  L5.u64_at RSEGS M ((V 2%nat) + 656) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 648) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 640) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 632) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 624) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 616) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 608) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 600) (V 48%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> ~ (1293512 <= i < 1293512 + 4) -> ~ (1293544 <= i < 1293544 + 8) -> ~ (1293552 <= i < 1293552 + 8) -> ~ (1293568 <= i < 1293568 + 8) -> ~ (1293600 <= i < 1293600 + 8) -> ~ (1293608 <= i < 1293608 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x120264 M) (st fx' R' 0x118878 M')
        /\ (forall x, In x KS_duGa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1147060
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 672)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 48%nat)
        /\ L5.u32_at RSEGS M' 1293512 5
        /\ L5.u64_at RSEGS M' 1293608 0
        /\ L5.u64_at RSEGS M' 1293600 6898968
        /\ L5.u64_at RSEGS M' 1293568 0
        /\ L5.u64_at RSEGS M' 1293552 0
        /\ L5.u64_at RSEGS M' 1293544 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 pvzI22 pvzI23 G2 G8 G9 G18 G19 G20 G21 G22 pvzI24 K1 K2 K3 K4 pvzI25 pvzI26 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV8l; move HV8l before pvzI2; pose proof (proj2 pvzI2) as HV8r; move HV8r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV9l; move HV9l before pvzI3; pose proof (proj2 pvzI3) as HV9r; move HV9r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV18l; move HV18l before pvzI4; pose proof (proj2 pvzI4) as HV18r; move HV18r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV19l; move HV19l before pvzI5; pose proof (proj2 pvzI5) as HV19r; move HV19r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV20l; move HV20l before pvzI6; pose proof (proj2 pvzI6) as HV20r; move HV20r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV21l; move HV21l before pvzI7; pose proof (proj2 pvzI7) as HV21r; move HV21r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV22l; move HV22l before pvzI8; pose proof (proj2 pvzI8) as HV22r; move HV22r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV33l; move HV33l before pvzI9; pose proof (proj2 pvzI9) as HV33r; move HV33r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV34l; move HV34l before pvzI10; pose proof (proj2 pvzI10) as HV34r; move HV34r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV40l; move HV40l before pvzI11; pose proof (proj2 pvzI11) as HV40r; move HV40r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV41l; move HV41l before pvzI12; pose proof (proj2 pvzI12) as HV41r; move HV41r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV42l; move HV42l before pvzI13; pose proof (proj2 pvzI13) as HV42r; move HV42r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV43l; move HV43l before pvzI14; pose proof (proj2 pvzI14) as HV43r; move HV43r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV44l; move HV44l before pvzI15; pose proof (proj2 pvzI15) as HV44r; move HV44r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV45l; move HV45l before pvzI16; pose proof (proj2 pvzI16) as HV45r; move HV45r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV46l; move HV46l before pvzI17; pose proof (proj2 pvzI17) as HV46r; move HV46r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV47l; move HV47l before pvzI18; pose proof (proj2 pvzI18) as HV47r; move HV47r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV48l; move HV48l before pvzI19; pose proof (proj2 pvzI19) as HV48r; move HV48r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV118l; move HV118l before pvzI20; pose proof (proj2 pvzI20) as HV118r; move HV118r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV119l; move HV119l before pvzI21; pose proof (proj2 pvzI21) as HV119r; move HV119r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as HV120l; move HV120l before pvzI22; pose proof (proj2 pvzI22) as HV120r; move HV120r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as HV122l; move HV122l before pvzI23; pose proof (proj2 pvzI23) as HV122r; move HV122r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K0l; move K0l before pvzI24; pose proof (proj2 pvzI24) as K0r; move K0r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K5l; move K5l before pvzI25; pose proof (proj2 pvzI25) as K5r; move K5r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K6l; move K6l before pvzI26; pose proof (proj2 pvzI26) as K6r; move K6r before pvzI26; clear pvzI26.
  set (vz_2 := V 2%nat) in *. set (vz_8 := V 8%nat) in *. set (vz_9 := V 9%nat) in *. set (vz_18 := V 18%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_20 := V 20%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_22 := V 22%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_118 := V 118%nat) in *. set (vz_119 := V 119%nat) in *. set (vz_120 := V 120%nat) in *. set (vz_122 := V 122%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 8%nat => Z_to_bv 64 vz_8 | 9%nat => Z_to_bv 64 vz_9 | 18%nat => Z_to_bv 64 vz_18 | 19%nat => Z_to_bv 64 vz_19 | 20%nat => Z_to_bv 64 vz_20 | 21%nat => Z_to_bv 64 vz_21 | 22%nat => Z_to_bv 64 vz_22 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 118%nat => Z_to_bv 64 vz_118 | 119%nat => Z_to_bv 64 vz_119 | 120%nat => Z_to_bv 64 vz_120 | 122%nat => Z_to_bv 64 vz_122 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 8%nat => vz_8 | 9%nat => vz_9 | 18%nat => vz_18 | 19%nat => vz_19 | 20%nat => vz_20 | 21%nat => vz_21 | 22%nat => vz_22 | 33%nat => vz_33 | 34%nat => vz_34 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 118%nat => vz_118 | 119%nat => vz_119 | 120%nat => vz_120 | 122%nat => vz_122 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 123%nat. }
  assert (HR: regs_ok E PduGa.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduGa.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduGa.kn0).
  { unfold know_ok, PduGa.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K47]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PduGa.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PduGa.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 16) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply Hfr. unfold PduGa.F0.
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
  change (SR.ps_pc PduGa.ps0) with 0x118878 in Hms. change (SR.ps_regs PduGa.ps0) with (map (fun i => (i, nth i PduGa.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduGa.ps0) with PduGa.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduGa.regs0 PduGa.regs_out0 140 KS_duGa KS_duGa_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduGb1 := LibSegBa_duGb1_b.
Definition KS_duGb1 : list nat := Eval vm_compute in (BG.kept_list 140 PduGb1.regs0 PduGb1.regs_out0).
Lemma KS_duGb1_ok : BG.kept_ok 140 PduGb1.regs0 PduGb1.regs_out0 KS_duGb1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma duGb1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 23%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 25%nat) < 2 ^ 64 -> 0 <= (V 26%nat) < 2 ^ 64 -> 0 <= (V 27%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 -> 0 <= (V 123%nat) < 2 ^ 64 -> 0 <= (V 124%nat) < 2 ^ 64 -> 0 <= (V 125%nat) < 2 ^ 64 -> 0 <= (V 127%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 7 -> getr R (reg 9) = Z_to_bv 64 1293512 -> getr R (reg 21) = Z_to_bv 64 6896960 -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) -> getr R (reg 23) = Z_to_bv 64 (V 123%nat) -> getr R (reg 24) = Z_to_bv 64 (V 124%nat) -> getr R (reg 25) = Z_to_bv 64 (V 125%nat) -> getr R (reg 26) = Z_to_bv 64 7 -> getr R (reg 27) = Z_to_bv 64 (V 127%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 672 -> L5.defined M ((V 2%nat) - 16) 672 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 67 <= (V 34%nat) <= 73 -> (((V 2%nat) - 16) + 672 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.writable RSEGS M 1293544 8 -> L5.writable RSEGS M 1293552 8 -> L5.writable RSEGS M 1293568 8 -> L5.u64_at RSEGS M 1293600 ((V 2%nat) + 672) ->
  L5.u64_at RSEGS M 1293608 80 -> L5.u64_at RSEGS M 6896960 (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 40) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 104) 1184784 ->
  L5.u64_at RSEGS M ((V 2%nat) + 96) 37 -> L5.u64_at RSEGS M ((V 2%nat) + 88) 2147483647 -> L5.u64_at RSEGS M ((V 2%nat) + 80) (2147483640 - (V 34%nat)) -> L5.u64_at RSEGS M ((V 2%nat) + 72) ((V 34%nat) + 7) ->
  L5.u64_at RSEGS M ((V 2%nat) + 64) 1293512 -> L5.u64_at RSEGS M ((V 2%nat) + 56) 90410 -> L5.u64_at RSEGS M ((V 2%nat) + 48) 7 -> L5.u64_at RSEGS M ((V 2%nat) + 208) 6896960 ->
  L5.u64_at RSEGS M ((V 2%nat) + 544) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 648) 1184288 -> L5.u64_at RSEGS M ((V 2%nat) + 640) 1293512 -> L5.u64_at RSEGS M ((V 2%nat) + 632) 90394 ->
  L5.u64_at RSEGS M ((V 2%nat) + 624) 6896960 -> L5.u64_at RSEGS M ((V 2%nat) + 616) 1 -> L5.u64_at RSEGS M ((V 2%nat) + 608) 6898968 -> L5.u64_at RSEGS M ((V 2%nat) + 600) 5 ->
  L5.u64_at RSEGS M ((V 2%nat) + 592) (V 22%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 584) (V 23%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 576) (V 24%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 568) (V 25%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 560) (V 26%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 552) (V 27%nat) -> L5.u64_at RSEGS M 1293584 1180112 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 672) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 672) -> ~ (1293544 <= i < 1293544 + 8) -> ~ (1293552 <= i < 1293552 + 8) -> ~ (1293568 <= i < 1293568 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x120264 M) (st fx' R' 0x12020c M')
        /\ (forall x, In x KS_duGb1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1184320
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 544)
        /\ getr R' (reg 8) = Z_to_bv 64 0
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 1180112
        /\ getr R' (reg 18) = Z_to_bv 64 6896960
        /\ getr R' (reg 19) = Z_to_bv 64 1
        /\ getr R' (reg 20) = Z_to_bv 64 6898968
        /\ getr R' (reg 22) = Z_to_bv 64 (V 22%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 23%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 25%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 26%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 27%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 584) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 592) (V 22%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 600) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 608) 6898968
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 616) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 624) 6896960
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 632) ((V 34%nat) + 14)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 640) 1293512
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 648) 1184320
        /\ L5.u64_at RSEGS M' 1293568 ((V 2%nat) + 672)
        /\ L5.u64_at RSEGS M' 1293552 ((V 2%nat) + 672)
        /\ L5.u64_at RSEGS M' 1293544 ((V 2%nat) + 752)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 544) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 576) (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 568) (V 25%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 560) (V 26%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 552) (V 27%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G21 G22 G23 G24 G25 G26 G27 pvzI16 K1 K2 K3 K4 pvzI17 pvzI18 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV22l; move HV22l before pvzI2; pose proof (proj2 pvzI2) as HV22r; move HV22r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV23l; move HV23l before pvzI3; pose proof (proj2 pvzI3) as HV23r; move HV23r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV24l; move HV24l before pvzI4; pose proof (proj2 pvzI4) as HV24r; move HV24r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV25l; move HV25l before pvzI5; pose proof (proj2 pvzI5) as HV25r; move HV25r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV26l; move HV26l before pvzI6; pose proof (proj2 pvzI6) as HV26r; move HV26r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV27l; move HV27l before pvzI7; pose proof (proj2 pvzI7) as HV27r; move HV27r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV33l; move HV33l before pvzI8; pose proof (proj2 pvzI8) as HV33r; move HV33r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV34l; move HV34l before pvzI9; pose proof (proj2 pvzI9) as HV34r; move HV34r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV122l; move HV122l before pvzI11; pose proof (proj2 pvzI11) as HV122r; move HV122r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV123l; move HV123l before pvzI12; pose proof (proj2 pvzI12) as HV123r; move HV123r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV124l; move HV124l before pvzI13; pose proof (proj2 pvzI13) as HV124r; move HV124r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV125l; move HV125l before pvzI14; pose proof (proj2 pvzI14) as HV125r; move HV125r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV127l; move HV127l before pvzI15; pose proof (proj2 pvzI15) as HV127r; move HV127r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K5l; move K5l before pvzI17; pose proof (proj2 pvzI17) as K5r; move K5r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K6l; move K6l before pvzI18; pose proof (proj2 pvzI18) as K6r; move K6r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_22 := V 22%nat) in *. set (vz_23 := V 23%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_25 := V 25%nat) in *. set (vz_26 := V 26%nat) in *. set (vz_27 := V 27%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_122 := V 122%nat) in *. set (vz_123 := V 123%nat) in *. set (vz_124 := V 124%nat) in *. set (vz_125 := V 125%nat) in *. set (vz_127 := V 127%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 22%nat => Z_to_bv 64 vz_22 | 23%nat => Z_to_bv 64 vz_23 | 24%nat => Z_to_bv 64 vz_24 | 25%nat => Z_to_bv 64 vz_25 | 26%nat => Z_to_bv 64 vz_26 | 27%nat => Z_to_bv 64 vz_27 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 40%nat => Z_to_bv 64 vz_40 | 122%nat => Z_to_bv 64 vz_122 | 123%nat => Z_to_bv 64 vz_123 | 124%nat => Z_to_bv 64 vz_124 | 125%nat => Z_to_bv 64 vz_125 | 127%nat => Z_to_bv 64 vz_127 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 22%nat => vz_22 | 23%nat => vz_23 | 24%nat => vz_24 | 25%nat => vz_25 | 26%nat => vz_26 | 27%nat => vz_27 | 33%nat => vz_33 | 34%nat => vz_34 | 40%nat => vz_40 | 122%nat => vz_122 | 123%nat => vz_123 | 124%nat => vz_124 | 125%nat => vz_125 | 127%nat => vz_127 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 128%nat. }
  assert (HR: regs_ok E PduGb1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduGb1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduGb1.kn0).
  { unfold know_ok, PduGb1.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV22l HV22r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV23l HV23r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV25l HV25r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV26l HV26r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV27l HV27r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K38]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PduGb1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PduGb1.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 672) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PduGb1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduGb1.ps0) with 0x12020c in Hms. change (SR.ps_regs PduGb1.ps0) with (map (fun i => (i, nth i PduGb1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduGb1.ps0) with PduGb1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduGb1.regs0 PduGb1.regs_out0 140 KS_duGb1 KS_duGb1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV22l HV22r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV24l HV24r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV25l HV25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV26l HV26r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV27l HV27r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduGb2 := LibSegBa_duGb2_b.
Definition KS_duGb2 : list nat := Eval vm_compute in (BG.kept_list 140 PduGb2.regs0 PduGb2.regs_out0).
Lemma KS_duGb2_ok : BG.kept_ok 140 PduGb2.regs0 PduGb2.regs_out0 KS_duGb2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma duGb2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 20%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 118%nat) < 2 ^ 64 -> 0 <= (V 119%nat) < 2 ^ 64 -> 0 <= (V 120%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 9) = Z_to_bv 64 1293512 -> getr R (reg 18) = Z_to_bv 64 (V 118%nat) -> getr R (reg 19) = Z_to_bv 64 (V 119%nat) -> getr R (reg 20) = Z_to_bv 64 (V 120%nat) -> getr R (reg 21) = Z_to_bv 64 6896960 -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.defined M ((V 2%nat) - 16) 16 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 67 <= (V 34%nat) <= 73 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.writable RSEGS M 1293512 4 -> L5.writable RSEGS M 1293544 8 -> L5.writable RSEGS M 1293552 8 -> L5.writable RSEGS M 1293568 8 ->
  L5.writable RSEGS M 1293600 8 -> L5.writable RSEGS M 1293608 8 -> L5.u64_at RSEGS M 1293600 ((V 2%nat) + 128) -> L5.u64_at RSEGS M 1293608 80 ->
  L5.u64_at RSEGS M 6896960 (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 40) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 104) 1184320 -> L5.u64_at RSEGS M ((V 2%nat) + 96) 1293512 ->
  L5.u64_at RSEGS M ((V 2%nat) + 88) ((V 34%nat) + 14) -> L5.u64_at RSEGS M ((V 2%nat) + 80) 6896960 -> L5.u64_at RSEGS M ((V 2%nat) + 72) 1 -> L5.u64_at RSEGS M ((V 2%nat) + 64) 6898968 ->
  L5.u64_at RSEGS M ((V 2%nat) + 56) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 48) (V 22%nat) -> L5.u32_at RSEGS M 1293512 5 -> L5.u64_at RSEGS M ((V 2%nat) + 416) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 472) 426864 -> L5.u64_at RSEGS M ((V 2%nat) + 464) 90394 -> L5.u64_at RSEGS M ((V 2%nat) + 456) 1293512 -> L5.u64_at RSEGS M ((V 2%nat) + 448) ((V 2%nat) + 544) ->
  L5.u64_at RSEGS M ((V 2%nat) + 440) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 432) (V 20%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 424) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 536) 687288 ->
  L5.u64_at RSEGS M ((V 2%nat) + 528) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 520) (V 9%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 512) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 664) 1147056 ->
  L5.u64_at RSEGS M ((V 2%nat) + 656) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 648) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 640) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 632) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 624) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 616) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 608) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 600) (V 48%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> ~ (1293512 <= i < 1293512 + 4) -> ~ (1293544 <= i < 1293544 + 8) -> ~ (1293552 <= i < 1293552 + 8) -> ~ (1293568 <= i < 1293568 + 8) -> ~ (1293600 <= i < 1293600 + 8) -> ~ (1293608 <= i < 1293608 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x120264 M) (st fx' R' 0x118878 M')
        /\ (forall x, In x KS_duGb2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1147060
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 672)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 48%nat)
        /\ L5.u32_at RSEGS M' 1293512 5
        /\ L5.u64_at RSEGS M' 1293608 0
        /\ L5.u64_at RSEGS M' 1293600 6898968
        /\ L5.u64_at RSEGS M' 1293568 0
        /\ L5.u64_at RSEGS M' 1293552 0
        /\ L5.u64_at RSEGS M' 1293544 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 pvzI22 pvzI23 G2 G8 G9 G18 G19 G20 G21 G22 pvzI24 K1 K2 K3 K4 pvzI25 pvzI26 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV8l; move HV8l before pvzI2; pose proof (proj2 pvzI2) as HV8r; move HV8r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV9l; move HV9l before pvzI3; pose proof (proj2 pvzI3) as HV9r; move HV9r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV18l; move HV18l before pvzI4; pose proof (proj2 pvzI4) as HV18r; move HV18r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV19l; move HV19l before pvzI5; pose proof (proj2 pvzI5) as HV19r; move HV19r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV20l; move HV20l before pvzI6; pose proof (proj2 pvzI6) as HV20r; move HV20r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV21l; move HV21l before pvzI7; pose proof (proj2 pvzI7) as HV21r; move HV21r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV22l; move HV22l before pvzI8; pose proof (proj2 pvzI8) as HV22r; move HV22r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV33l; move HV33l before pvzI9; pose proof (proj2 pvzI9) as HV33r; move HV33r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV34l; move HV34l before pvzI10; pose proof (proj2 pvzI10) as HV34r; move HV34r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV40l; move HV40l before pvzI11; pose proof (proj2 pvzI11) as HV40r; move HV40r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV41l; move HV41l before pvzI12; pose proof (proj2 pvzI12) as HV41r; move HV41r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV42l; move HV42l before pvzI13; pose proof (proj2 pvzI13) as HV42r; move HV42r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV43l; move HV43l before pvzI14; pose proof (proj2 pvzI14) as HV43r; move HV43r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV44l; move HV44l before pvzI15; pose proof (proj2 pvzI15) as HV44r; move HV44r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV45l; move HV45l before pvzI16; pose proof (proj2 pvzI16) as HV45r; move HV45r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV46l; move HV46l before pvzI17; pose proof (proj2 pvzI17) as HV46r; move HV46r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV47l; move HV47l before pvzI18; pose proof (proj2 pvzI18) as HV47r; move HV47r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV48l; move HV48l before pvzI19; pose proof (proj2 pvzI19) as HV48r; move HV48r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV118l; move HV118l before pvzI20; pose proof (proj2 pvzI20) as HV118r; move HV118r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV119l; move HV119l before pvzI21; pose proof (proj2 pvzI21) as HV119r; move HV119r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as HV120l; move HV120l before pvzI22; pose proof (proj2 pvzI22) as HV120r; move HV120r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as HV122l; move HV122l before pvzI23; pose proof (proj2 pvzI23) as HV122r; move HV122r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K0l; move K0l before pvzI24; pose proof (proj2 pvzI24) as K0r; move K0r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K5l; move K5l before pvzI25; pose proof (proj2 pvzI25) as K5r; move K5r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K6l; move K6l before pvzI26; pose proof (proj2 pvzI26) as K6r; move K6r before pvzI26; clear pvzI26.
  set (vz_2 := V 2%nat) in *. set (vz_8 := V 8%nat) in *. set (vz_9 := V 9%nat) in *. set (vz_18 := V 18%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_20 := V 20%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_22 := V 22%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_118 := V 118%nat) in *. set (vz_119 := V 119%nat) in *. set (vz_120 := V 120%nat) in *. set (vz_122 := V 122%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 8%nat => Z_to_bv 64 vz_8 | 9%nat => Z_to_bv 64 vz_9 | 18%nat => Z_to_bv 64 vz_18 | 19%nat => Z_to_bv 64 vz_19 | 20%nat => Z_to_bv 64 vz_20 | 21%nat => Z_to_bv 64 vz_21 | 22%nat => Z_to_bv 64 vz_22 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 118%nat => Z_to_bv 64 vz_118 | 119%nat => Z_to_bv 64 vz_119 | 120%nat => Z_to_bv 64 vz_120 | 122%nat => Z_to_bv 64 vz_122 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 8%nat => vz_8 | 9%nat => vz_9 | 18%nat => vz_18 | 19%nat => vz_19 | 20%nat => vz_20 | 21%nat => vz_21 | 22%nat => vz_22 | 33%nat => vz_33 | 34%nat => vz_34 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 118%nat => vz_118 | 119%nat => vz_119 | 120%nat => vz_120 | 122%nat => vz_122 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 123%nat. }
  assert (HR: regs_ok E PduGb2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduGb2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduGb2.kn0).
  { unfold know_ok, PduGb2.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K47]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PduGb2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PduGb2.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 16) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply Hfr. unfold PduGb2.F0.
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
  change (SR.ps_pc PduGb2.ps0) with 0x118878 in Hms. change (SR.ps_regs PduGb2.ps0) with (map (fun i => (i, nth i PduGb2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduGb2.ps0) with PduGb2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduGb2.regs0 PduGb2.regs_out0 140 KS_duGb2 KS_duGb2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduEc := LibSegBa_duEc_b.
Definition KS_duEc : list nat := Eval vm_compute in (BG.kept_list 140 PduEc.regs0 PduEc.regs_out0).
Lemma KS_duEc_ok : BG.kept_ok 140 PduEc.regs0 PduEc.regs_out0 KS_duEc = true. Proof. vm_compute. reflexivity. Qed.
Lemma duEc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 23%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 25%nat) < 2 ^ 64 -> 0 <= (V 26%nat) < 2 ^ 64 -> 0 <= (V 27%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 -> 0 <= (V 123%nat) < 2 ^ 64 -> 0 <= (V 125%nat) < 2 ^ 64 -> 0 <= (V 127%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 9) = Z_to_bv 64 1293512 -> getr R (reg 21) = Z_to_bv 64 6896960 -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) -> getr R (reg 23) = Z_to_bv 64 (V 123%nat) -> getr R (reg 24) = Z_to_bv 64 0 -> getr R (reg 25) = Z_to_bv 64 (V 125%nat) -> getr R (reg 26) = Z_to_bv 64 (V 34%nat) -> getr R (reg 27) = Z_to_bv 64 (V 127%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 2112) 2800 -> L5.defined M ((V 2%nat) - 2112) 2800 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 74 <= (V 34%nat) <= 131071 -> (((V 2%nat) - 2112) + 2800 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 2112)) ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147450950) 24 -> L5.u64_at RSEGS M 2147462176 0 -> L5.writable RSEGS M 1293544 8 -> L5.writable RSEGS M 1293552 8 ->
  L5.writable RSEGS M 1293568 8 -> L5.u64_at RSEGS M 1293600 ((V 2%nat) + 672) -> L5.u64_at RSEGS M 1293608 80 -> L5.u64_at RSEGS M 6896960 (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 40) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 104) 1187376 -> L5.u64_at RSEGS M ((V 2%nat) + 96) 37 -> L5.u64_at RSEGS M ((V 2%nat) + 88) 2147483647 ->
  L5.u64_at RSEGS M ((V 2%nat) + 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 72) 7 -> L5.u64_at RSEGS M ((V 2%nat) + 64) 1293512 -> L5.u64_at RSEGS M ((V 2%nat) + 56) 90403 ->
  L5.u64_at RSEGS M ((V 2%nat) + 48) 0 -> L5.u8_at RSEGS M 1293512 5 -> L5.u32_at RSEGS M 1293656 4294967295 -> L5.u8_at RSEGS M 1313049 1 ->
  L5.u64_at RSEGS M 1309752 2147450880 -> L5.u64_at RSEGS M 1283272 1218816 -> L5.u64_at RSEGS M ((V 2%nat) + 208) 6896960 -> L5.u64_at RSEGS M ((V 2%nat) + 544) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 648) 1184288 -> L5.u64_at RSEGS M ((V 2%nat) + 640) 1293512 -> L5.u64_at RSEGS M ((V 2%nat) + 632) 90394 -> L5.u64_at RSEGS M ((V 2%nat) + 624) 6896960 ->
  L5.u64_at RSEGS M ((V 2%nat) + 616) 1 -> L5.u64_at RSEGS M ((V 2%nat) + 608) 6898968 -> L5.u64_at RSEGS M ((V 2%nat) + 600) 5 -> L5.u64_at RSEGS M ((V 2%nat) + 592) (V 22%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 584) (V 23%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 576) (V 24%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 568) (V 25%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 560) (V 26%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 552) (V 27%nat) -> L5.u64_at RSEGS M 1293584 1180112 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 2112) <= bv_unsigned a < ((V 2%nat) - 2112) + 2800) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 2112) <= i < ((V 2%nat) - 2112) + 2800) -> ~ (1293544 <= i < 1293544 + 8) -> ~ (1293552 <= i < 1293552 + 8) -> ~ (1293568 <= i < 1293568 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x120264 M) (st fx' R' 0x12020c M')
        /\ (forall x, In x KS_duEc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1184320
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 544)
        /\ getr R' (reg 8) = Z_to_bv 64 0
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 1180112
        /\ getr R' (reg 14) = Z_to_bv 64 84
        /\ getr R' (reg 15) = Z_to_bv 64 10
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 2%nat) + 679)
        /\ getr R' (reg 18) = Z_to_bv 64 6896960
        /\ getr R' (reg 19) = Z_to_bv 64 1
        /\ getr R' (reg 20) = Z_to_bv 64 6898968
        /\ getr R' (reg 22) = Z_to_bv 64 (V 22%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 23%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 25%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 26%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 27%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 584) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 592) (V 22%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 600) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 608) 6898968
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 616) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 624) 6896960
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 632) ((V 34%nat) + 14)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 640) 1293512
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 648) 1184320
        /\ L5.u64_at RSEGS M' 1293552 ((V 2%nat) + 679)
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 678) 10
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 677) 84
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 676) 85
        /\ L5.u32_at RSEGS M' ((V 2%nat) + 672) 1347307808
        /\ L5.u64_at RSEGS M' 1293568 ((V 2%nat) + 672)
        /\ L5.u64_at RSEGS M' 1293544 ((V 2%nat) + 752)
        /\ L5.defined M' ((V 2%nat) + 656) 16
        /\ L5.defined M' ((V 2%nat) + 679) 9
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 544) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 576) (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 568) (V 25%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 560) (V 26%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 552) (V 27%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 G2 G8 G9 G21 G22 G23 G24 G25 G26 G27 pvzI15 K1 K2 K3 K4 pvzI16 pvzI17 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV22l; move HV22l before pvzI2; pose proof (proj2 pvzI2) as HV22r; move HV22r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV23l; move HV23l before pvzI3; pose proof (proj2 pvzI3) as HV23r; move HV23r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV24l; move HV24l before pvzI4; pose proof (proj2 pvzI4) as HV24r; move HV24r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV25l; move HV25l before pvzI5; pose proof (proj2 pvzI5) as HV25r; move HV25r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV26l; move HV26l before pvzI6; pose proof (proj2 pvzI6) as HV26r; move HV26r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV27l; move HV27l before pvzI7; pose proof (proj2 pvzI7) as HV27r; move HV27r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV33l; move HV33l before pvzI8; pose proof (proj2 pvzI8) as HV33r; move HV33r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV34l; move HV34l before pvzI9; pose proof (proj2 pvzI9) as HV34r; move HV34r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV40l; move HV40l before pvzI10; pose proof (proj2 pvzI10) as HV40r; move HV40r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV122l; move HV122l before pvzI11; pose proof (proj2 pvzI11) as HV122r; move HV122r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV123l; move HV123l before pvzI12; pose proof (proj2 pvzI12) as HV123r; move HV123r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV125l; move HV125l before pvzI13; pose proof (proj2 pvzI13) as HV125r; move HV125r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV127l; move HV127l before pvzI14; pose proof (proj2 pvzI14) as HV127r; move HV127r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K0l; move K0l before pvzI15; pose proof (proj2 pvzI15) as K0r; move K0r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K5l; move K5l before pvzI16; pose proof (proj2 pvzI16) as K5r; move K5r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K6l; move K6l before pvzI17; pose proof (proj2 pvzI17) as K6r; move K6r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_22 := V 22%nat) in *. set (vz_23 := V 23%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_25 := V 25%nat) in *. set (vz_26 := V 26%nat) in *. set (vz_27 := V 27%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_122 := V 122%nat) in *. set (vz_123 := V 123%nat) in *. set (vz_125 := V 125%nat) in *. set (vz_127 := V 127%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 22%nat => Z_to_bv 64 vz_22 | 23%nat => Z_to_bv 64 vz_23 | 24%nat => Z_to_bv 64 vz_24 | 25%nat => Z_to_bv 64 vz_25 | 26%nat => Z_to_bv 64 vz_26 | 27%nat => Z_to_bv 64 vz_27 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 40%nat => Z_to_bv 64 vz_40 | 122%nat => Z_to_bv 64 vz_122 | 123%nat => Z_to_bv 64 vz_123 | 125%nat => Z_to_bv 64 vz_125 | 127%nat => Z_to_bv 64 vz_127 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 22%nat => vz_22 | 23%nat => vz_23 | 24%nat => vz_24 | 25%nat => vz_25 | 26%nat => vz_26 | 27%nat => vz_27 | 33%nat => vz_33 | 34%nat => vz_34 | 40%nat => vz_40 | 122%nat => vz_122 | 123%nat => vz_123 | 125%nat => vz_125 | 127%nat => vz_127 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 128%nat. }
  assert (HR: regs_ok E PduEc.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduEc.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduEc.kn0).
  { unfold know_ok, PduEc.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV22l HV22r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV23l HV23r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV25l HV25r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV26l HV26r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV27l HV27r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K45]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PduEc.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PduEc.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 2112) <= bv_unsigned a < (vz_2 - 2112) + 2800) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PduEc.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduEc.ps0) with 0x12020c in Hms. change (SR.ps_regs PduEc.ps0) with (map (fun i => (i, nth i PduEc.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduEc.ps0) with PduEc.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduEc.regs0 PduEc.regs_out0 140 KS_duEc KS_duEc_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV22l HV22r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { apply u32_of_u8x4; [clear; lia | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 16); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia] | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia] | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia] | eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 19); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 20); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV24l HV24r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV25l HV25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV26l HV26r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV27l HV27r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduGc := LibSegBa_duGc_b.
Definition KS_duGc : list nat := Eval vm_compute in (BG.kept_list 140 PduGc.regs0 PduGc.regs_out0).
Lemma KS_duGc_ok : BG.kept_ok 140 PduGc.regs0 PduGc.regs_out0 KS_duGc = true. Proof. vm_compute. reflexivity. Qed.
Lemma duGc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 20%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 118%nat) < 2 ^ 64 -> 0 <= (V 119%nat) < 2 ^ 64 -> 0 <= (V 120%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 9) = Z_to_bv 64 1293512 -> getr R (reg 18) = Z_to_bv 64 (V 118%nat) -> getr R (reg 19) = Z_to_bv 64 (V 119%nat) -> getr R (reg 20) = Z_to_bv 64 (V 120%nat) -> getr R (reg 21) = Z_to_bv 64 6896960 -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.defined M ((V 2%nat) - 16) 16 ->
  L5.img_clear M 65536 1282048 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 74 <= (V 34%nat) <= 131071 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.writable RSEGS M 1293512 4 -> L5.writable RSEGS M 1293544 8 -> L5.writable RSEGS M 1293552 8 -> L5.writable RSEGS M 1293568 8 ->
  L5.writable RSEGS M 1293600 8 -> L5.writable RSEGS M 1293608 8 -> L5.u64_at RSEGS M 1293600 ((V 2%nat) + 128) -> L5.u64_at RSEGS M 1293608 80 ->
  L5.u64_at RSEGS M 6896960 (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 40) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 104) 1184320 -> L5.u64_at RSEGS M ((V 2%nat) + 96) 1293512 ->
  L5.u64_at RSEGS M ((V 2%nat) + 88) ((V 34%nat) + 14) -> L5.u64_at RSEGS M ((V 2%nat) + 80) 6896960 -> L5.u64_at RSEGS M ((V 2%nat) + 72) 1 -> L5.u64_at RSEGS M ((V 2%nat) + 64) 6898968 ->
  L5.u64_at RSEGS M ((V 2%nat) + 56) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 48) (V 22%nat) -> L5.u32_at RSEGS M 1293512 5 -> L5.u64_at RSEGS M ((V 2%nat) + 416) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 472) 426864 -> L5.u64_at RSEGS M ((V 2%nat) + 464) 90394 -> L5.u64_at RSEGS M ((V 2%nat) + 456) 1293512 -> L5.u64_at RSEGS M ((V 2%nat) + 448) ((V 2%nat) + 544) ->
  L5.u64_at RSEGS M ((V 2%nat) + 440) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 432) (V 20%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 424) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 536) 687288 ->
  L5.u64_at RSEGS M ((V 2%nat) + 528) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 520) (V 9%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 512) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 664) 1147056 ->
  L5.u64_at RSEGS M ((V 2%nat) + 656) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 648) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 640) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 632) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 624) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 616) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 608) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 600) (V 48%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> ~ (1293512 <= i < 1293512 + 4) -> ~ (1293544 <= i < 1293544 + 8) -> ~ (1293552 <= i < 1293552 + 8) -> ~ (1293568 <= i < 1293568 + 8) -> ~ (1293600 <= i < 1293600 + 8) -> ~ (1293608 <= i < 1293608 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x120264 M) (st fx' R' 0x118878 M')
        /\ (forall x, In x KS_duGc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 1147060
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 672)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 48%nat)
        /\ L5.u32_at RSEGS M' 1293512 5
        /\ L5.u64_at RSEGS M' 1293608 0
        /\ L5.u64_at RSEGS M' 1293600 6898968
        /\ L5.u64_at RSEGS M' 1293568 0
        /\ L5.u64_at RSEGS M' 1293552 0
        /\ L5.u64_at RSEGS M' 1293544 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 pvzI22 pvzI23 G2 G8 G9 G18 G19 G20 G21 G22 pvzI24 K1 K2 K3 K4 pvzI25 pvzI26 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV8l; move HV8l before pvzI2; pose proof (proj2 pvzI2) as HV8r; move HV8r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV9l; move HV9l before pvzI3; pose proof (proj2 pvzI3) as HV9r; move HV9r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV18l; move HV18l before pvzI4; pose proof (proj2 pvzI4) as HV18r; move HV18r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV19l; move HV19l before pvzI5; pose proof (proj2 pvzI5) as HV19r; move HV19r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV20l; move HV20l before pvzI6; pose proof (proj2 pvzI6) as HV20r; move HV20r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV21l; move HV21l before pvzI7; pose proof (proj2 pvzI7) as HV21r; move HV21r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV22l; move HV22l before pvzI8; pose proof (proj2 pvzI8) as HV22r; move HV22r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV33l; move HV33l before pvzI9; pose proof (proj2 pvzI9) as HV33r; move HV33r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV34l; move HV34l before pvzI10; pose proof (proj2 pvzI10) as HV34r; move HV34r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV40l; move HV40l before pvzI11; pose proof (proj2 pvzI11) as HV40r; move HV40r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV41l; move HV41l before pvzI12; pose proof (proj2 pvzI12) as HV41r; move HV41r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV42l; move HV42l before pvzI13; pose proof (proj2 pvzI13) as HV42r; move HV42r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV43l; move HV43l before pvzI14; pose proof (proj2 pvzI14) as HV43r; move HV43r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV44l; move HV44l before pvzI15; pose proof (proj2 pvzI15) as HV44r; move HV44r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV45l; move HV45l before pvzI16; pose proof (proj2 pvzI16) as HV45r; move HV45r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV46l; move HV46l before pvzI17; pose proof (proj2 pvzI17) as HV46r; move HV46r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV47l; move HV47l before pvzI18; pose proof (proj2 pvzI18) as HV47r; move HV47r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV48l; move HV48l before pvzI19; pose proof (proj2 pvzI19) as HV48r; move HV48r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV118l; move HV118l before pvzI20; pose proof (proj2 pvzI20) as HV118r; move HV118r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV119l; move HV119l before pvzI21; pose proof (proj2 pvzI21) as HV119r; move HV119r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as HV120l; move HV120l before pvzI22; pose proof (proj2 pvzI22) as HV120r; move HV120r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as HV122l; move HV122l before pvzI23; pose proof (proj2 pvzI23) as HV122r; move HV122r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K0l; move K0l before pvzI24; pose proof (proj2 pvzI24) as K0r; move K0r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K5l; move K5l before pvzI25; pose proof (proj2 pvzI25) as K5r; move K5r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K6l; move K6l before pvzI26; pose proof (proj2 pvzI26) as K6r; move K6r before pvzI26; clear pvzI26.
  set (vz_2 := V 2%nat) in *. set (vz_8 := V 8%nat) in *. set (vz_9 := V 9%nat) in *. set (vz_18 := V 18%nat) in *. set (vz_19 := V 19%nat) in *. set (vz_20 := V 20%nat) in *. set (vz_21 := V 21%nat) in *. set (vz_22 := V 22%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_118 := V 118%nat) in *. set (vz_119 := V 119%nat) in *. set (vz_120 := V 120%nat) in *. set (vz_122 := V 122%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 8%nat => Z_to_bv 64 vz_8 | 9%nat => Z_to_bv 64 vz_9 | 18%nat => Z_to_bv 64 vz_18 | 19%nat => Z_to_bv 64 vz_19 | 20%nat => Z_to_bv 64 vz_20 | 21%nat => Z_to_bv 64 vz_21 | 22%nat => Z_to_bv 64 vz_22 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 118%nat => Z_to_bv 64 vz_118 | 119%nat => Z_to_bv 64 vz_119 | 120%nat => Z_to_bv 64 vz_120 | 122%nat => Z_to_bv 64 vz_122 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 8%nat => vz_8 | 9%nat => vz_9 | 18%nat => vz_18 | 19%nat => vz_19 | 20%nat => vz_20 | 21%nat => vz_21 | 22%nat => vz_22 | 33%nat => vz_33 | 34%nat => vz_34 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 118%nat => vz_118 | 119%nat => vz_119 | 120%nat => vz_120 | 122%nat => vz_122 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 123%nat. }
  assert (HR: regs_ok E PduGc.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduGc.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduGc.kn0).
  { unfold know_ok, PduGc.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K47]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PduGc.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PduGc.NX0 with 140%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 16) <= bv_unsigned a < (vz_2 - 16) + 16) -> ~ (1293512 <= bv_unsigned a < 1293512 + 4) -> ~ (1293544 <= bv_unsigned a < 1293544 + 8) -> ~ (1293552 <= bv_unsigned a < 1293552 + 8) -> ~ (1293568 <= bv_unsigned a < 1293568 + 8) -> ~ (1293600 <= bv_unsigned a < 1293600 + 8) -> ~ (1293608 <= bv_unsigned a < 1293608 + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply Hfr. unfold PduGc.F0.
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
  change (SR.ps_pc PduGc.ps0) with 0x118878 in Hms. change (SR.ps_regs PduGc.ps0) with (map (fun i => (i, nth i PduGc.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduGc.ps0) with PduGc.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduGc.regs0 PduGc.regs_out0 140 KS_duGc KS_duGc_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End AS0DIAGUP.
