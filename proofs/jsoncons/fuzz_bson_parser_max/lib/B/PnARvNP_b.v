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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_awvN6_b LibSegBa_awvN10_b LibSegBa_awvU_b LibSegBa_awvUc_b LibSegBa_awvC3_b LibSegBa_awvC3r_b LibSegBa_awvC4_b LibSegBa_awvC4r_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARVNP.
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
Module PawvN6 := LibSegBa_awvN6_b.
Definition KS_awvN6 : list nat := Eval vm_compute in (BG.kept_list 80 PawvN6.regs0 PawvN6.regs_out0).
Lemma KS_awvN6_ok : BG.kept_ok 80 PawvN6.regs0 PawvN6.regs_out0 KS_awvN6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvN6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  6905856 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> ((V 50%nat) + 512 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 50%nat)) -> ((V 51%nat) + 1 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 51%nat)) ->
  L5.u64_at RSEGS M (V 34%nat) 1251456 -> L5KA.zeros_at M 2147607325 1 -> ((((V 34%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 34%nat) / 8) + 2147450880)) -> L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  L5.u8_at RSEGS M ((V 33%nat) + 10) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0b8c M) (st fx' R' 0x7b90c M')
        /\ (forall x, In x KS_awvN6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726080
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 692900
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 1
        /\ L5.defined M' ((V 50%nat) + 8) 504).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 pvzI9 K14 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 pvzI11 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K32l; move K32l before pvzI11; pose proof (proj2 pvzI11) as K32r; move K32r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvN6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvN6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvN6.kn0).
  { unfold know_ok, PawvN6.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42; lia | clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42; lia | clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42; lia | clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42; lia | exactA K40]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | byte_tac ltac:(clear) | exactA K44]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvN6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvN6.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 64) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PawvN6.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvN6.ps0) with 0x7b90c in Hms. change (SR.ps_regs PawvN6.ps0) with (map (fun i => (i, nth i PawvN6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvN6.ps0) with PawvN6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvN6.regs0 PawvN6.regs_out0 80 KS_awvN6 KS_awvN6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvN6.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvN6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvN6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvN6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvN6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvN6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvN6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvN6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvN6.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvN6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvN6.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PawvN6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvN10 := LibSegBa_awvN10_b.
Definition KS_awvN10 : list nat := Eval vm_compute in (BG.kept_list 80 PawvN10.regs0 PawvN10.regs_out0).
Lemma KS_awvN10_ok : BG.kept_ok 80 PawvN10.regs0 PawvN10.regs_out0 KS_awvN10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvN10_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  6905856 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> ((V 50%nat) + 512 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 50%nat)) -> ((V 51%nat) + 1 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 51%nat)) ->
  L5.u64_at RSEGS M (V 34%nat) 1251456 -> L5KA.zeros_at M 2147607325 1 -> ((((V 34%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 34%nat) / 8) + 2147450880)) -> L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  L5.u8_at RSEGS M ((V 33%nat) + 10) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0d2c M) (st fx' R' 0x7b90c M')
        /\ (forall x, In x KS_awvN10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726080
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 692900
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 1
        /\ L5.defined M' ((V 50%nat) + 8) 504).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 pvzI9 K14 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 pvzI11 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K32l; move K32l before pvzI11; pose proof (proj2 pvzI11) as K32r; move K32r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvN10.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvN10.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvN10.kn0).
  { unfold know_ok, PawvN10.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42; lia | clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42; lia | clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K12 K24 K25 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27 K31 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42; lia | clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42; lia | exactA K40]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K32l K32r K34 K36 K37 K38 K39 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37; lia | byte_tac ltac:(clear) | exactA K44]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvN10.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvN10.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 64) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PawvN10.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvN10.ps0) with 0x7b90c in Hms. change (SR.ps_regs PawvN10.ps0) with (map (fun i => (i, nth i PawvN10.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvN10.ps0) with PawvN10.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvN10.regs0 PawvN10.regs_out0 80 KS_awvN10 KS_awvN10_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvN10.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvN10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvN10.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvN10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvN10.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvN10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvN10.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvN10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvN10.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PawvN10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvN10.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PawvN10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 K37) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 K38 K42) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvU := LibSegBa_awvU_b.
Definition KS_awvU : list nat := Eval vm_compute in (BG.kept_list 80 PawvU.regs0 PawvU.regs_out0).
Lemma KS_awvU_ok : BG.kept_ok 80 PawvU.regs0 PawvU.regs_out0 KS_awvU = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvU_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487392 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb03bc M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_awvU -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 721864
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 14).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G21 G22 G26 G27 pvzI6 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvU.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvU.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvU.kn0).
  { unfold know_ok, PawvU.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvU.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvU.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvU.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvU.ps0) with 0xae848 in Hms. change (SR.ps_regs PawvU.ps0) with (map (fun i => (i, nth i PawvU.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvU.ps0) with PawvU.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvU.regs0 PawvU.regs_out0 80 KS_awvU KS_awvU_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvU.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvU.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvU.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvU.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvUc := LibSegBa_awvUc_b.
Definition KS_awvUc : list nat := Eval vm_compute in (BG.kept_list 80 PawvUc.regs0 PawvUc.regs_out0).
Lemma KS_awvUc_ok : BG.kept_ok 80 PawvUc.regs0 PawvUc.regs_out0 KS_awvUc = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvUc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487392 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M ((((V 33%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 400) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 512 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 50%nat) + 504) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 512 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) -> (65536 + 6840320 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 64 <= 65536) -> (65536 + 6840320 <= (V 51%nat) \/ (V 51%nat) + 1 <= 65536) ->
  L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 64) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb03c8 M) (st fx' R' 0x7b90c M')
        /\ (forall x, In x KS_awvUc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 726080
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 0
        /\ L5.defined M' ((V 50%nat) + 8) 504).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G22 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 pvzI9 K14 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PawvUc.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvUc.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvUc.kn0).
  { unfold know_ok, PawvUc.kn0.
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
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvUc.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvUc.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 64) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PawvUc.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvUc.ps0) with 0x7b90c in Hms. change (SR.ps_regs PawvUc.ps0) with (map (fun i => (i, nth i PawvUc.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvUc.ps0) with PawvUc.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvUc.regs0 PawvUc.regs_out0 80 KS_awvUc KS_awvUc_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvUc.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvUc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvUc.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvUc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvUc.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvUc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K12 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 K29 K30) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvC3 := LibSegBa_awvC3_b.
Definition KS_awvC3 : list nat := Eval vm_compute in (BG.kept_list 80 PawvC3.regs0 PawvC3.regs_out0).
Lemma KS_awvC3_ok : BG.kept_ok 80 PawvC3.regs0 PawvC3.regs_out0 KS_awvC3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvC3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487392 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0664 M) (st fx' R' 0xae924 M')
        /\ (forall x, In x KS_awvC3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 722548
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G21 G22 G26 G27 pvzI6 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvC3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvC3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvC3.kn0).
  { unfold know_ok, PawvC3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvC3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvC3.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvC3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvC3.ps0) with 0xae924 in Hms. change (SR.ps_regs PawvC3.ps0) with (map (fun i => (i, nth i PawvC3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvC3.ps0) with PawvC3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvC3.regs0 PawvC3.regs_out0 80 KS_awvC3 KS_awvC3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvC3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvC3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvC3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvC3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvC3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvC3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvC3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvC3.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvC3r := LibSegBa_awvC3r_b.
Definition KS_awvC3r : list nat := Eval vm_compute in (BG.kept_list 80 PawvC3r.regs0 PawvC3r.regs_out0).
Lemma KS_awvC3r_ok : BG.kept_ok 80 PawvC3r.regs0 PawvC3r.regs_out0 KS_awvC3r = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvC3r_conc fx R M (V : nat -> Z) :
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
    /\ (msteps RSEGS (st fx R 0xb0674 M) (st fx' R' 0x7b90c M')
        /\ (forall x, In x KS_awvC3r -> getr R' (reg x) = getr R (reg x))
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
  assert (HR: regs_ok E PawvC3r.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvC3r.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvC3r.kn0).
  { unfold know_ok, PawvC3r.kn0.
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
  pvz_hg ltac:(idtac; destruct (PawvC3r.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvC3r.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PawvC3r.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvC3r.ps0) with 0x7b90c in Hms. change (SR.ps_regs PawvC3r.ps0) with (map (fun i => (i, nth i PawvC3r.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvC3r.ps0) with PawvC3r.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvC3r.regs0 PawvC3r.regs_out0 80 KS_awvC3r KS_awvC3r_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvC3r.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvC3r.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvC3r.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvC3r.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvC3r.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvC3r.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvC4 := LibSegBa_awvC4_b.
Definition KS_awvC4 : list nat := Eval vm_compute in (BG.kept_list 80 PawvC4.regs0 PawvC4.regs_out0).
Lemma KS_awvC4_ok : BG.kept_ok 80 PawvC4.regs0 PawvC4.regs_out0 KS_awvC4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvC4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 26) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487392 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb0890 M) (st fx' R' 0xb37a8 M')
        /\ (forall x, In x KS_awvC4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 723104
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G21 G22 G26 G27 pvzI6 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PawvC4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvC4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvC4.kn0).
  { unfold know_ok, PawvC4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PawvC4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvC4.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PawvC4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvC4.ps0) with 0xb37a8 in Hms. change (SR.ps_regs PawvC4.ps0) with (map (fun i => (i, nth i PawvC4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvC4.ps0) with PawvC4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvC4.regs0 PawvC4.regs_out0 80 KS_awvC4 KS_awvC4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvC4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvC4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvC4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvC4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvC4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvC4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PawvC4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PawvC4.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PawvC4r := LibSegBa_awvC4r_b.
Definition KS_awvC4r : list nat := Eval vm_compute in (BG.kept_list 80 PawvC4r.regs0 PawvC4r.regs_out0).
Lemma KS_awvC4r_ok : BG.kept_ok 80 PawvC4r.regs0 PawvC4r.regs_out0 KS_awvC4r = true. Proof. vm_compute. reflexivity. Qed.
Lemma awvC4r_conc fx R M (V : nat -> Z) :
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
    /\ (msteps RSEGS (st fx R 0xb08a0 M) (st fx' R' 0x7b90c M')
        /\ (forall x, In x KS_awvC4r -> getr R' (reg x) = getr R (reg x))
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
  assert (HR: regs_ok E PawvC4r.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PawvC4r.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PawvC4r.kn0).
  { unfold know_ok, PawvC4r.kn0.
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
  pvz_hg ltac:(idtac; destruct (PawvC4r.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PawvC4r.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PawvC4r.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PawvC4r.ps0) with 0x7b90c in Hms. change (SR.ps_regs PawvC4r.ps0) with (map (fun i => (i, nth i PawvC4r.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PawvC4r.ps0) with PawvC4r.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PawvC4r.regs0 PawvC4r.regs_out0 80 KS_awvC4r KS_awvC4r_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PawvC4r.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PawvC4r.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvC4r.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PawvC4r.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PawvC4r.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PawvC4r.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PNARVNP.
