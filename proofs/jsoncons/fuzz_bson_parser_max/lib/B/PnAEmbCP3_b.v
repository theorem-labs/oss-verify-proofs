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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_azcI0_b LibSegBa_azcI1_b LibSegBa_azcI2_b LibSegBa_azcI3_b LibSegBa_azcI4_b LibSegBa_azcI5_b LibSegBa_azcI6_b LibSegBa_azcI7_b LibSegBa_azcI8_b LibSegBa_azcI9_b LibSegBa_azcI10_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAECP3.
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
Module PazcI0 := LibSegBa_azcI0_b.
Definition KS_azcI0 : list nat := Eval vm_compute in (BG.kept_list 60 PazcI0.regs0 PazcI0.regs_out0).
Lemma KS_azcI0_ok : BG.kept_ok 60 PazcI0.regs0 PazcI0.regs_out0 KS_azcI0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcI0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 40) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 40) -> 4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355248 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 80) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (((V 40%nat) + 40) + 40) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 40) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 731412 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 176) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 24%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad7f4 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azcI0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 80)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 80)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 80)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 40%nat) + 80)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731412
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 80)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (((V 40%nat) + 40) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 40)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 pvzI18 K1 K2 K3 K4 K5 K6 pvzI19 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI20 K18 pvzI21 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV24l; move HV24l before pvzI2; pose proof (proj2 pvzI2) as HV24r; move HV24r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV49l; move HV49l before pvzI14; pose proof (proj2 pvzI14) as HV49r; move HV49r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV50l; move HV50l before pvzI15; pose proof (proj2 pvzI15) as HV50r; move HV50r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV51l; move HV51l before pvzI16; pose proof (proj2 pvzI16) as HV51r; move HV51r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K7l; move K7l before pvzI19; pose proof (proj2 pvzI19) as K7r; move K7r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K17l; move K17l before pvzI20; pose proof (proj2 pvzI20) as K17r; move K17r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 24%nat => Z_to_bv 64 vz_24 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 24%nat => vz_24 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcI0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcI0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcI0.kn0).
  { unfold know_ok, PazcI0.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K43]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcI0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcI0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 176) <= bv_unsigned a < (vz_2 - 176) + 176) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PazcI0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcI0.ps0) with 0x7ba7c in Hms. change (SR.ps_regs PazcI0.ps0) with (map (fun i => (i, nth i PazcI0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcI0.ps0) with PazcI0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcI0.regs0 PazcI0.regs_out0 60 KS_azcI0 KS_azcI0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PazcI0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcI1 := LibSegBa_azcI1_b.
Definition KS_azcI1 : list nat := Eval vm_compute in (BG.kept_list 60 PazcI1.regs0 PazcI1.regs_out0).
Lemma KS_azcI1_ok : BG.kept_ok 60 PazcI1.regs0 PazcI1.regs_out0 KS_azcI1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcI1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 80) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 80) -> 4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355248 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 160) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (((V 40%nat) + 80) + 40) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 80) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 731412 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 176) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 24%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad7f4 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azcI1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 160)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 160)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 120)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 40%nat) + 120)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731412
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 160)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (((V 40%nat) + 80) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 80)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 pvzI18 K1 K2 K3 K4 K5 K6 pvzI19 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI20 K18 pvzI21 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV24l; move HV24l before pvzI2; pose proof (proj2 pvzI2) as HV24r; move HV24r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV49l; move HV49l before pvzI14; pose proof (proj2 pvzI14) as HV49r; move HV49r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV50l; move HV50l before pvzI15; pose proof (proj2 pvzI15) as HV50r; move HV50r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV51l; move HV51l before pvzI16; pose proof (proj2 pvzI16) as HV51r; move HV51r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K7l; move K7l before pvzI19; pose proof (proj2 pvzI19) as K7r; move K7r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K17l; move K17l before pvzI20; pose proof (proj2 pvzI20) as K17r; move K17r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 24%nat => Z_to_bv 64 vz_24 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 24%nat => vz_24 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcI1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcI1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcI1.kn0).
  { unfold know_ok, PazcI1.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K43]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcI1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcI1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 176) <= bv_unsigned a < (vz_2 - 176) + 176) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PazcI1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcI1.ps0) with 0x7ba7c in Hms. change (SR.ps_regs PazcI1.ps0) with (map (fun i => (i, nth i PazcI1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcI1.ps0) with PazcI1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcI1.regs0 PazcI1.regs_out0 60 KS_azcI1 KS_azcI1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PazcI1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcI2 := LibSegBa_azcI2_b.
Definition KS_azcI2 : list nat := Eval vm_compute in (BG.kept_list 60 PazcI2.regs0 PazcI2.regs_out0).
Lemma KS_azcI2_ok : BG.kept_ok 60 PazcI2.regs0 PazcI2.regs_out0 KS_azcI2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcI2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 160) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 160) -> 4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355248 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 320) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (((V 40%nat) + 160) + 40) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 160) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 731412 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 176) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 24%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad7f4 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azcI2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 320)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 320)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 200)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 40%nat) + 200)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731412
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 320)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (((V 40%nat) + 160) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 160)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 pvzI18 K1 K2 K3 K4 K5 K6 pvzI19 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI20 K18 pvzI21 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV24l; move HV24l before pvzI2; pose proof (proj2 pvzI2) as HV24r; move HV24r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV49l; move HV49l before pvzI14; pose proof (proj2 pvzI14) as HV49r; move HV49r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV50l; move HV50l before pvzI15; pose proof (proj2 pvzI15) as HV50r; move HV50r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV51l; move HV51l before pvzI16; pose proof (proj2 pvzI16) as HV51r; move HV51r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K7l; move K7l before pvzI19; pose proof (proj2 pvzI19) as K7r; move K7r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K17l; move K17l before pvzI20; pose proof (proj2 pvzI20) as K17r; move K17r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 24%nat => Z_to_bv 64 vz_24 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 24%nat => vz_24 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcI2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcI2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcI2.kn0).
  { unfold know_ok, PazcI2.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K43]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcI2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcI2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 176) <= bv_unsigned a < (vz_2 - 176) + 176) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PazcI2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcI2.ps0) with 0x7ba7c in Hms. change (SR.ps_regs PazcI2.ps0) with (map (fun i => (i, nth i PazcI2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcI2.ps0) with PazcI2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcI2.regs0 PazcI2.regs_out0 60 KS_azcI2 KS_azcI2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PazcI2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcI3 := LibSegBa_azcI3_b.
Definition KS_azcI3 : list nat := Eval vm_compute in (BG.kept_list 60 PazcI3.regs0 PazcI3.regs_out0).
Lemma KS_azcI3_ok : BG.kept_ok 60 PazcI3.regs0 PazcI3.regs_out0 KS_azcI3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcI3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 320) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 320) -> 4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355248 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 640) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (((V 40%nat) + 320) + 40) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 320) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 731412 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 176) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 24%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad7f4 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azcI3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 640)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 640)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 360)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 40%nat) + 360)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731412
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 640)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (((V 40%nat) + 320) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 320)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 pvzI18 K1 K2 K3 K4 K5 K6 pvzI19 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI20 K18 pvzI21 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV24l; move HV24l before pvzI2; pose proof (proj2 pvzI2) as HV24r; move HV24r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV49l; move HV49l before pvzI14; pose proof (proj2 pvzI14) as HV49r; move HV49r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV50l; move HV50l before pvzI15; pose proof (proj2 pvzI15) as HV50r; move HV50r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV51l; move HV51l before pvzI16; pose proof (proj2 pvzI16) as HV51r; move HV51r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K7l; move K7l before pvzI19; pose proof (proj2 pvzI19) as K7r; move K7r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K17l; move K17l before pvzI20; pose proof (proj2 pvzI20) as K17r; move K17r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 24%nat => Z_to_bv 64 vz_24 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 24%nat => vz_24 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcI3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcI3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcI3.kn0).
  { unfold know_ok, PazcI3.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K43]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcI3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcI3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 176) <= bv_unsigned a < (vz_2 - 176) + 176) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PazcI3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcI3.ps0) with 0x7ba7c in Hms. change (SR.ps_regs PazcI3.ps0) with (map (fun i => (i, nth i PazcI3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcI3.ps0) with PazcI3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcI3.regs0 PazcI3.regs_out0 60 KS_azcI3 KS_azcI3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI3.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PazcI3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcI4 := LibSegBa_azcI4_b.
Definition KS_azcI4 : list nat := Eval vm_compute in (BG.kept_list 60 PazcI4.regs0 PazcI4.regs_out0).
Lemma KS_azcI4_ok : BG.kept_ok 60 PazcI4.regs0 PazcI4.regs_out0 KS_azcI4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcI4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 640) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 640) -> 4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355248 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 1280) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (((V 40%nat) + 640) + 40) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 640) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 731412 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 176) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 24%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad7f4 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azcI4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 1280)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 1280)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 680)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 40%nat) + 680)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731412
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 1280)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (((V 40%nat) + 640) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 640)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 pvzI18 K1 K2 K3 K4 K5 K6 pvzI19 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI20 K18 pvzI21 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV24l; move HV24l before pvzI2; pose proof (proj2 pvzI2) as HV24r; move HV24r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV49l; move HV49l before pvzI14; pose proof (proj2 pvzI14) as HV49r; move HV49r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV50l; move HV50l before pvzI15; pose proof (proj2 pvzI15) as HV50r; move HV50r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV51l; move HV51l before pvzI16; pose proof (proj2 pvzI16) as HV51r; move HV51r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K7l; move K7l before pvzI19; pose proof (proj2 pvzI19) as K7r; move K7r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K17l; move K17l before pvzI20; pose proof (proj2 pvzI20) as K17r; move K17r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 24%nat => Z_to_bv 64 vz_24 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 24%nat => vz_24 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcI4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcI4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcI4.kn0).
  { unfold know_ok, PazcI4.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K43]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcI4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcI4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 176) <= bv_unsigned a < (vz_2 - 176) + 176) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PazcI4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcI4.ps0) with 0x7ba7c in Hms. change (SR.ps_regs PazcI4.ps0) with (map (fun i => (i, nth i PazcI4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcI4.ps0) with PazcI4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcI4.regs0 PazcI4.regs_out0 60 KS_azcI4 KS_azcI4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI4.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PazcI4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcI5 := LibSegBa_azcI5_b.
Definition KS_azcI5 : list nat := Eval vm_compute in (BG.kept_list 60 PazcI5.regs0 PazcI5.regs_out0).
Lemma KS_azcI5_ok : BG.kept_ok 60 PazcI5.regs0 PazcI5.regs_out0 KS_azcI5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcI5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 1280) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 1280) -> 4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355248 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 2560) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (((V 40%nat) + 1280) + 40) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 1280) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 731412 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 176) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 24%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad7f4 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azcI5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 2560)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 2560)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 1320)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 40%nat) + 1320)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731412
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 2560)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (((V 40%nat) + 1280) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 1280)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 pvzI18 K1 K2 K3 K4 K5 K6 pvzI19 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI20 K18 pvzI21 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV24l; move HV24l before pvzI2; pose proof (proj2 pvzI2) as HV24r; move HV24r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV49l; move HV49l before pvzI14; pose proof (proj2 pvzI14) as HV49r; move HV49r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV50l; move HV50l before pvzI15; pose proof (proj2 pvzI15) as HV50r; move HV50r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV51l; move HV51l before pvzI16; pose proof (proj2 pvzI16) as HV51r; move HV51r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K7l; move K7l before pvzI19; pose proof (proj2 pvzI19) as K7r; move K7r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K17l; move K17l before pvzI20; pose proof (proj2 pvzI20) as K17r; move K17r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 24%nat => Z_to_bv 64 vz_24 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 24%nat => vz_24 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcI5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcI5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcI5.kn0).
  { unfold know_ok, PazcI5.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K43]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcI5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcI5.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 176) <= bv_unsigned a < (vz_2 - 176) + 176) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PazcI5.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcI5.ps0) with 0x7ba7c in Hms. change (SR.ps_regs PazcI5.ps0) with (map (fun i => (i, nth i PazcI5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcI5.ps0) with PazcI5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcI5.regs0 PazcI5.regs_out0 60 KS_azcI5 KS_azcI5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI5.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PazcI5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcI6 := LibSegBa_azcI6_b.
Definition KS_azcI6 : list nat := Eval vm_compute in (BG.kept_list 60 PazcI6.regs0 PazcI6.regs_out0).
Lemma KS_azcI6_ok : BG.kept_ok 60 PazcI6.regs0 PazcI6.regs_out0 KS_azcI6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcI6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 2560) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 2560) -> 4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355248 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 5120) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (((V 40%nat) + 2560) + 40) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 2560) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 731412 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 176) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 24%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad7f4 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azcI6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 5120)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 5120)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 2600)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 40%nat) + 2600)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731412
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 5120)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (((V 40%nat) + 2560) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 2560)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 pvzI18 K1 K2 K3 K4 K5 K6 pvzI19 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI20 K18 pvzI21 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV24l; move HV24l before pvzI2; pose proof (proj2 pvzI2) as HV24r; move HV24r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV49l; move HV49l before pvzI14; pose proof (proj2 pvzI14) as HV49r; move HV49r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV50l; move HV50l before pvzI15; pose proof (proj2 pvzI15) as HV50r; move HV50r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV51l; move HV51l before pvzI16; pose proof (proj2 pvzI16) as HV51r; move HV51r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K7l; move K7l before pvzI19; pose proof (proj2 pvzI19) as K7r; move K7r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K17l; move K17l before pvzI20; pose proof (proj2 pvzI20) as K17r; move K17r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 24%nat => Z_to_bv 64 vz_24 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 24%nat => vz_24 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcI6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcI6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcI6.kn0).
  { unfold know_ok, PazcI6.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K43]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcI6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcI6.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 176) <= bv_unsigned a < (vz_2 - 176) + 176) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PazcI6.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcI6.ps0) with 0x7ba7c in Hms. change (SR.ps_regs PazcI6.ps0) with (map (fun i => (i, nth i PazcI6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcI6.ps0) with PazcI6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcI6.regs0 PazcI6.regs_out0 60 KS_azcI6 KS_azcI6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI6.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PazcI6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcI7 := LibSegBa_azcI7_b.
Definition KS_azcI7 : list nat := Eval vm_compute in (BG.kept_list 60 PazcI7.regs0 PazcI7.regs_out0).
Lemma KS_azcI7_ok : BG.kept_ok 60 PazcI7.regs0 PazcI7.regs_out0 KS_azcI7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcI7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 5120) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 5120) -> 4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355248 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 10240) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (((V 40%nat) + 5120) + 40) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 5120) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 731412 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 176) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 24%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad7f4 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azcI7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 10240)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 10240)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 5160)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 40%nat) + 5160)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731412
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 10240)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (((V 40%nat) + 5120) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 5120)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 pvzI18 K1 K2 K3 K4 K5 K6 pvzI19 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI20 K18 pvzI21 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV24l; move HV24l before pvzI2; pose proof (proj2 pvzI2) as HV24r; move HV24r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV49l; move HV49l before pvzI14; pose proof (proj2 pvzI14) as HV49r; move HV49r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV50l; move HV50l before pvzI15; pose proof (proj2 pvzI15) as HV50r; move HV50r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV51l; move HV51l before pvzI16; pose proof (proj2 pvzI16) as HV51r; move HV51r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K7l; move K7l before pvzI19; pose proof (proj2 pvzI19) as K7r; move K7r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K17l; move K17l before pvzI20; pose proof (proj2 pvzI20) as K17r; move K17r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 24%nat => Z_to_bv 64 vz_24 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 24%nat => vz_24 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcI7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcI7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcI7.kn0).
  { unfold know_ok, PazcI7.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K43]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcI7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcI7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 176) <= bv_unsigned a < (vz_2 - 176) + 176) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PazcI7.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcI7.ps0) with 0x7ba7c in Hms. change (SR.ps_regs PazcI7.ps0) with (map (fun i => (i, nth i PazcI7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcI7.ps0) with PazcI7.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcI7.regs0 PazcI7.regs_out0 60 KS_azcI7 KS_azcI7_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI7.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PazcI7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcI8 := LibSegBa_azcI8_b.
Definition KS_azcI8 : list nat := Eval vm_compute in (BG.kept_list 60 PazcI8.regs0 PazcI8.regs_out0).
Lemma KS_azcI8_ok : BG.kept_ok 60 PazcI8.regs0 PazcI8.regs_out0 KS_azcI8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcI8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 10240) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 10240) -> 4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355248 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 20480) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (((V 40%nat) + 10240) + 40) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 10240) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 731412 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 176) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 24%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad7f4 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azcI8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 20480)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 20480)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 10280)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 40%nat) + 10280)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731412
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 20480)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (((V 40%nat) + 10240) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 10240)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 pvzI18 K1 K2 K3 K4 K5 K6 pvzI19 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI20 K18 pvzI21 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV24l; move HV24l before pvzI2; pose proof (proj2 pvzI2) as HV24r; move HV24r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV49l; move HV49l before pvzI14; pose proof (proj2 pvzI14) as HV49r; move HV49r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV50l; move HV50l before pvzI15; pose proof (proj2 pvzI15) as HV50r; move HV50r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV51l; move HV51l before pvzI16; pose proof (proj2 pvzI16) as HV51r; move HV51r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K7l; move K7l before pvzI19; pose proof (proj2 pvzI19) as K7r; move K7r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K17l; move K17l before pvzI20; pose proof (proj2 pvzI20) as K17r; move K17r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 24%nat => Z_to_bv 64 vz_24 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 24%nat => vz_24 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcI8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcI8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcI8.kn0).
  { unfold know_ok, PazcI8.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K43]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcI8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcI8.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 176) <= bv_unsigned a < (vz_2 - 176) + 176) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PazcI8.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcI8.ps0) with 0x7ba7c in Hms. change (SR.ps_regs PazcI8.ps0) with (map (fun i => (i, nth i PazcI8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcI8.ps0) with PazcI8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcI8.regs0 PazcI8.regs_out0 60 KS_azcI8 KS_azcI8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI8.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PazcI8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcI9 := LibSegBa_azcI9_b.
Definition KS_azcI9 : list nat := Eval vm_compute in (BG.kept_list 60 PazcI9.regs0 PazcI9.regs_out0).
Lemma KS_azcI9_ok : BG.kept_ok 60 PazcI9.regs0 PazcI9.regs_out0 KS_azcI9 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcI9_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 20480) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 20480) -> 4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355248 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 40960) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (((V 40%nat) + 20480) + 40) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 20480) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 731412 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 176) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 24%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad7f4 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azcI9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 40960)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 40960)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 20520)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 40%nat) + 20520)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731412
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 40960)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (((V 40%nat) + 20480) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 20480)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 pvzI18 K1 K2 K3 K4 K5 K6 pvzI19 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI20 K18 pvzI21 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV24l; move HV24l before pvzI2; pose proof (proj2 pvzI2) as HV24r; move HV24r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV49l; move HV49l before pvzI14; pose proof (proj2 pvzI14) as HV49r; move HV49r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV50l; move HV50l before pvzI15; pose proof (proj2 pvzI15) as HV50r; move HV50r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV51l; move HV51l before pvzI16; pose proof (proj2 pvzI16) as HV51r; move HV51r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K7l; move K7l before pvzI19; pose proof (proj2 pvzI19) as K7r; move K7r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K17l; move K17l before pvzI20; pose proof (proj2 pvzI20) as K17r; move K17r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 24%nat => Z_to_bv 64 vz_24 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 24%nat => vz_24 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcI9.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcI9.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcI9.kn0).
  { unfold know_ok, PazcI9.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K43]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcI9.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcI9.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 176) <= bv_unsigned a < (vz_2 - 176) + 176) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PazcI9.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcI9.ps0) with 0x7ba7c in Hms. change (SR.ps_regs PazcI9.ps0) with (map (fun i => (i, nth i PazcI9.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcI9.ps0) with PazcI9.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcI9.regs0 PazcI9.regs_out0 60 KS_azcI9 KS_azcI9_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI9.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PazcI9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazcI10 := LibSegBa_azcI10_b.
Definition KS_azcI10 : list nat := Eval vm_compute in (BG.kept_list 60 PazcI10.regs0 PazcI10.regs_out0).
Lemma KS_azcI10_ok : BG.kept_ok 60 PazcI10.regs0 PazcI10.regs_out0 KS_azcI10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azcI10_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 40960) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 40960) -> 4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 4096 <= (V 40%nat) <= 140737488355248 ->
  aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 81920) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (((V 40%nat) + 40960) + 40) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 40%nat) + 40960) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 731412 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 176) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 24%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 176) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad7f4 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azcI10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 81920)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 81920)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 41000)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 40%nat) + 41000)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 731412
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 81920)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (((V 40%nat) + 40960) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 36%nat) + 40960)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 pvzI18 K1 K2 K3 K4 K5 K6 pvzI19 K8 K9 K10 K11 K12 K13 K14 K15 K16 pvzI20 K18 pvzI21 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV24l; move HV24l before pvzI2; pose proof (proj2 pvzI2) as HV24r; move HV24r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV33l; move HV33l before pvzI3; pose proof (proj2 pvzI3) as HV33r; move HV33r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV34l; move HV34l before pvzI4; pose proof (proj2 pvzI4) as HV34r; move HV34r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV35l; move HV35l before pvzI5; pose proof (proj2 pvzI5) as HV35r; move HV35r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV36l; move HV36l before pvzI6; pose proof (proj2 pvzI6) as HV36r; move HV36r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV44l; move HV44l before pvzI9; pose proof (proj2 pvzI9) as HV44r; move HV44r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV45l; move HV45l before pvzI10; pose proof (proj2 pvzI10) as HV45r; move HV45r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV46l; move HV46l before pvzI11; pose proof (proj2 pvzI11) as HV46r; move HV46r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV47l; move HV47l before pvzI12; pose proof (proj2 pvzI12) as HV47r; move HV47r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV48l; move HV48l before pvzI13; pose proof (proj2 pvzI13) as HV48r; move HV48r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV49l; move HV49l before pvzI14; pose proof (proj2 pvzI14) as HV49r; move HV49r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV50l; move HV50l before pvzI15; pose proof (proj2 pvzI15) as HV50r; move HV50r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV51l; move HV51l before pvzI16; pose proof (proj2 pvzI16) as HV51r; move HV51r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K0l; move K0l before pvzI18; pose proof (proj2 pvzI18) as K0r; move K0r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K7l; move K7l before pvzI19; pose proof (proj2 pvzI19) as K7r; move K7r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K17l; move K17l before pvzI20; pose proof (proj2 pvzI20) as K17r; move K17r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_24 := V 24%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 24%nat => Z_to_bv 64 vz_24 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 24%nat => vz_24 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PazcI10.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PazcI10.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PazcI10.kn0).
  { unfold know_ok, PazcI10.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | clear - HV33l HV33r K7l K7r K9 K11 K12; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K17l K17r) | clear; lia | exact K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K43]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PazcI10.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PazcI10.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 176) <= bv_unsigned a < (vz_2 - 176) + 176) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 24) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PazcI10.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PazcI10.ps0) with 0x7ba7c in Hms. change (SR.ps_regs PazcI10.ps0) with (map (fun i => (i, nth i PazcI10.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PazcI10.ps0) with PazcI10.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PazcI10.regs0 PazcI10.regs_out0 60 KS_azcI10 KS_azcI10_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PazcI10.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PazcI10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K17l K17r) | clear; lia].
Qed.
(* [comment removed for export] *)

End PNAECP3.
