(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BigLinkZA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Eb0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_058S9 BndP_Eb_059S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMBSLTP3.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).

Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
  intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5KA.zpolyA_sound E Vz e z A Pz)).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, BL.MM. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.

Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u64_of_KWord8; eauto. Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u32_of_KWord4; eauto. Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof. intros K Ha Hv Hr ->. eapply L5K.u8_of_KWord1; eauto. Qed.

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

Local Ltac solve_modk k :=
  repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].

Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.

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

Local Ltac den_tac := first [reflexivity | lia | idtac].

Local Ltac apc_norm :=
  repeat match goal with
  | |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
  | |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
  | |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
  | |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
  end.

Local Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
  repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Local Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].

Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].

Module PbstG0 := BndP_Eb_058S9.LibSegEb_bstG0.
Definition KS_bstG0 : list nat := Eval vm_compute in (BG.kept_list 60 PbstG0.regs0 PbstG0.regs_out0).
Lemma KS_bstG0_ok : BG.kept_ok 60 PbstG0.regs0 PbstG0.regs_out0 KS_bstG0 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bstG0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 9) = Z_to_bv 64 2 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 32) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 32) ->
  4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 16 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  6930432 <= (V 35%nat) <= 140737488355320 -> aligned (V 35%nat) 8 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 8 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 8 <= (V 33%nat)) ->
  0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 18446744073709551615 -> 6930432 <= (V 52%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  L5.u8_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 4096)) -> aligned (V 52%nat) 8 -> L5.u8_at RSEGS M (((V 52%nat) / 8) + 2147450880) 1 ->
  ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 1 <= (V 33%nat)) -> 0 <= (V 53%nat) <= 255 -> 4096 <= (V 40%nat) <= 140737488355264 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 32) 32 -> L5KA.zeros_at M ((((V 40%nat) + 32) / 8) + 2147450880) 4 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 32) \/ ((V 40%nat) + 32) + 32 <= 2147446784) -> 4096 <= ((V 40%nat) + 32) <= 140737488355296 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 32) \/ ((V 40%nat) + 32) + 32 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 40%nat) + 32) \/ ((V 40%nat) + 32) + 32 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 32) \/ ((V 40%nat) + 32) + 32 <= (V 34%nat)) -> ((V 35%nat) + 8 <= ((V 40%nat) + 32) \/ ((V 40%nat) + 32) + 32 <= (V 35%nat)) ->
  (65536 + 6864896 <= ((V 40%nat) + 32) \/ ((V 40%nat) + 32) + 32 <= 65536) -> ((V 52%nat) + 1 <= ((V 40%nat) + 32) \/ ((V 40%nat) + 32) + 32 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 770868 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 32) + 0) <= bv_unsigned a < (((V 40%nat) + 32) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 32) + 0) <= i < (((V 40%nat) + 32) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb56a4 M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x KS_bstG0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 698784
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 32)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 32)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) ((V 2%nat) - 104)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 743392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 771064
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + 64)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 56) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 48) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 40) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 32) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 40%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI19 K1 K2 K3 K4 K5 K6 pvzI20 K8 K9 K10 K11 K12 K13 K14 K15 pvzI21 K17 pvzI22 K19 K20 K21 K22 K23 pvzI23 K25 K26 K27 K28 K29 K30 K31 pvzI24 pvzI25 pvzI26 K35 K36 K37 K38 K39 K40 pvzI27 pvzI28 K43 K44 K45 K46 pvzI29 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV43l; move HV43l before pvzI9; pose proof (proj2 pvzI9) as HV43r; move HV43r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV44l; move HV44l before pvzI10; pose proof (proj2 pvzI10) as HV44r; move HV44r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV45l; move HV45l before pvzI11; pose proof (proj2 pvzI11) as HV45r; move HV45r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV46l; move HV46l before pvzI12; pose proof (proj2 pvzI12) as HV46r; move HV46r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV47l; move HV47l before pvzI13; pose proof (proj2 pvzI13) as HV47r; move HV47r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV48l; move HV48l before pvzI14; pose proof (proj2 pvzI14) as HV48r; move HV48r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV49l; move HV49l before pvzI15; pose proof (proj2 pvzI15) as HV49r; move HV49r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV50l; move HV50l before pvzI16; pose proof (proj2 pvzI16) as HV50r; move HV50r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV53l; move HV53l before pvzI18; pose proof (proj2 pvzI18) as HV53r; move HV53r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K7l; move K7l before pvzI20; pose proof (proj2 pvzI20) as K7r; move K7r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K18l; move K18l before pvzI22; pose proof (proj2 pvzI22) as K18r; move K18r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K24l; move K24l before pvzI23; pose proof (proj2 pvzI23) as K24r; move K24r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K32l; move K32l before pvzI24; pose proof (proj2 pvzI24) as K32r; move K32r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K33l; move K33l before pvzI25; pose proof (proj2 pvzI25) as K33r; move K33r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K34l; move K34l before pvzI26; pose proof (proj2 pvzI26) as K34r; move K34r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K41l; move K41l before pvzI27; pose proof (proj2 pvzI27) as K41r; move K41r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K42l; move K42l before pvzI28; pose proof (proj2 pvzI28) as K42r; move K42r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K47l; move K47l before pvzI29; pose proof (proj2 pvzI29) as K47r; move K47r before pvzI29; clear pvzI29.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 52%nat => vz_52 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbstG0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstG0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstG0.kn0).
  { unfold know_ok, PbstG0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear) | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K47l K47r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K70]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstG0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstG0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 240) -> ~ (((vz_40 + 32) + 0) <= bv_unsigned a < ((vz_40 + 32) + 0) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbstG0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstG0.ps0) with 0x7cc28 in Hms. change (SR.ps_regs PbstG0.ps0) with (map (fun i => (i, nth i PbstG0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstG0.ps0) with PbstG0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstG0.regs0 PbstG0.regs_out0 60 KS_bstG0 KS_bstG0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstG0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbstG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbstG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbstG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbstG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbstG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbstG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbstG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG0.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbstG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbstG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbstG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbstG0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K41l K41r) | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K33l K33r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K32l K32r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbstG1 := BndP_Eb_059S9.LibSegEb_bstG1.
Definition KS_bstG1 : list nat := Eval vm_compute in (BG.kept_list 60 PbstG1.regs0 PbstG1.regs_out0).
Lemma KS_bstG1_ok : BG.kept_ok 60 PbstG1.regs0 PbstG1.regs_out0 KS_bstG1 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bstG1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 9) = Z_to_bv 64 4 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 19) = Z_to_bv 64 2 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 64) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 64) ->
  4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 16 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  6930432 <= (V 35%nat) <= 140737488355320 -> aligned (V 35%nat) 8 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 8 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 8 <= (V 33%nat)) ->
  0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 18446744073709551615 -> 6930432 <= (V 52%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  L5.u8_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 4096)) -> aligned (V 52%nat) 8 -> L5.u8_at RSEGS M (((V 52%nat) / 8) + 2147450880) 1 ->
  ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 1 <= (V 33%nat)) -> 0 <= (V 53%nat) <= 255 -> 4096 <= (V 40%nat) <= 140737488355200 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 64) 32 -> L5KA.zeros_at M ((((V 40%nat) + 64) / 8) + 2147450880) 4 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 64) \/ ((V 40%nat) + 64) + 32 <= 2147446784) -> 4096 <= ((V 40%nat) + 64) <= 140737488355296 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 64) \/ ((V 40%nat) + 64) + 32 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 40%nat) + 64) \/ ((V 40%nat) + 64) + 32 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 64) \/ ((V 40%nat) + 64) + 32 <= (V 34%nat)) -> ((V 35%nat) + 8 <= ((V 40%nat) + 64) \/ ((V 40%nat) + 64) + 32 <= (V 35%nat)) ->
  (65536 + 6864896 <= ((V 40%nat) + 64) \/ ((V 40%nat) + 64) + 32 <= 65536) -> ((V 52%nat) + 1 <= ((V 40%nat) + 64) \/ ((V 40%nat) + 64) + 32 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 770868 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 64) + 0) <= bv_unsigned a < (((V 40%nat) + 64) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 64) + 0) <= i < (((V 40%nat) + 64) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb56a4 M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x KS_bstG1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 698784
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 64)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 64)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 64)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) ((V 2%nat) - 104)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 743392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 771064
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + 96)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 88) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 80) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 72) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 64) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 128)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 40%nat) + 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI19 K1 K2 K3 K4 K5 K6 pvzI20 K8 K9 K10 K11 K12 K13 K14 K15 pvzI21 K17 pvzI22 K19 K20 K21 K22 K23 pvzI23 K25 K26 K27 K28 K29 K30 K31 pvzI24 pvzI25 pvzI26 K35 K36 K37 K38 K39 K40 pvzI27 pvzI28 K43 K44 K45 K46 pvzI29 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV43l; move HV43l before pvzI9; pose proof (proj2 pvzI9) as HV43r; move HV43r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV44l; move HV44l before pvzI10; pose proof (proj2 pvzI10) as HV44r; move HV44r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV45l; move HV45l before pvzI11; pose proof (proj2 pvzI11) as HV45r; move HV45r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV46l; move HV46l before pvzI12; pose proof (proj2 pvzI12) as HV46r; move HV46r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV47l; move HV47l before pvzI13; pose proof (proj2 pvzI13) as HV47r; move HV47r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV48l; move HV48l before pvzI14; pose proof (proj2 pvzI14) as HV48r; move HV48r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV49l; move HV49l before pvzI15; pose proof (proj2 pvzI15) as HV49r; move HV49r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV50l; move HV50l before pvzI16; pose proof (proj2 pvzI16) as HV50r; move HV50r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV53l; move HV53l before pvzI18; pose proof (proj2 pvzI18) as HV53r; move HV53r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K7l; move K7l before pvzI20; pose proof (proj2 pvzI20) as K7r; move K7r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K18l; move K18l before pvzI22; pose proof (proj2 pvzI22) as K18r; move K18r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K24l; move K24l before pvzI23; pose proof (proj2 pvzI23) as K24r; move K24r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K32l; move K32l before pvzI24; pose proof (proj2 pvzI24) as K32r; move K32r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K33l; move K33l before pvzI25; pose proof (proj2 pvzI25) as K33r; move K33r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K34l; move K34l before pvzI26; pose proof (proj2 pvzI26) as K34r; move K34r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K41l; move K41l before pvzI27; pose proof (proj2 pvzI27) as K41r; move K41r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K42l; move K42l before pvzI28; pose proof (proj2 pvzI28) as K42r; move K42r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K47l; move K47l before pvzI29; pose proof (proj2 pvzI29) as K47r; move K47r before pvzI29; clear pvzI29.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 52%nat => vz_52 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbstG1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstG1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstG1.kn0).
  { unfold know_ok, PbstG1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear) | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K47l K47r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K70]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstG1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstG1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 240) -> ~ (((vz_40 + 64) + 0) <= bv_unsigned a < ((vz_40 + 64) + 0) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbstG1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstG1.ps0) with 0x7cc28 in Hms. change (SR.ps_regs PbstG1.ps0) with (map (fun i => (i, nth i PbstG1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstG1.ps0) with PbstG1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstG1.regs0 PbstG1.regs_out0 60 KS_bstG1 KS_bstG1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstG1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbstG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbstG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbstG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbstG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbstG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbstG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG1.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbstG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG1.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbstG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbstG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbstG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbstG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K41l K41r) | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K33l K33r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K32l K32r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbstG2 := BndP_Eb_059S9.LibSegEb_bstG2.
Definition KS_bstG2 : list nat := Eval vm_compute in (BG.kept_list 60 PbstG2.regs0 PbstG2.regs_out0).
Lemma KS_bstG2_ok : BG.kept_ok 60 PbstG2.regs0 PbstG2.regs_out0 KS_bstG2 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bstG2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 9) = Z_to_bv 64 8 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 19) = Z_to_bv 64 4 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 128) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 128) ->
  4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 16 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  6930432 <= (V 35%nat) <= 140737488355320 -> aligned (V 35%nat) 8 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 8 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 8 <= (V 33%nat)) ->
  0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 18446744073709551615 -> 6930432 <= (V 52%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  L5.u8_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 4096)) -> aligned (V 52%nat) 8 -> L5.u8_at RSEGS M (((V 52%nat) / 8) + 2147450880) 1 ->
  ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 1 <= (V 33%nat)) -> 0 <= (V 53%nat) <= 255 -> 4096 <= (V 40%nat) <= 140737488355072 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 128) 32 -> L5KA.zeros_at M ((((V 40%nat) + 128) / 8) + 2147450880) 4 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 128) \/ ((V 40%nat) + 128) + 32 <= 2147446784) -> 4096 <= ((V 40%nat) + 128) <= 140737488355296 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 128) \/ ((V 40%nat) + 128) + 32 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 40%nat) + 128) \/ ((V 40%nat) + 128) + 32 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 128) \/ ((V 40%nat) + 128) + 32 <= (V 34%nat)) -> ((V 35%nat) + 8 <= ((V 40%nat) + 128) \/ ((V 40%nat) + 128) + 32 <= (V 35%nat)) ->
  (65536 + 6864896 <= ((V 40%nat) + 128) \/ ((V 40%nat) + 128) + 32 <= 65536) -> ((V 52%nat) + 1 <= ((V 40%nat) + 128) \/ ((V 40%nat) + 128) + 32 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 770868 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 128) + 0) <= bv_unsigned a < (((V 40%nat) + 128) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 128) + 0) <= i < (((V 40%nat) + 128) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb56a4 M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x KS_bstG2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 698784
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 128)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 128)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 128)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) ((V 2%nat) - 104)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 743392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 771064
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + 160)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 152) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 144) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 136) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 128) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 256)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 40%nat) + 128)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI19 K1 K2 K3 K4 K5 K6 pvzI20 K8 K9 K10 K11 K12 K13 K14 K15 pvzI21 K17 pvzI22 K19 K20 K21 K22 K23 pvzI23 K25 K26 K27 K28 K29 K30 K31 pvzI24 pvzI25 pvzI26 K35 K36 K37 K38 K39 K40 pvzI27 pvzI28 K43 K44 K45 K46 pvzI29 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV43l; move HV43l before pvzI9; pose proof (proj2 pvzI9) as HV43r; move HV43r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV44l; move HV44l before pvzI10; pose proof (proj2 pvzI10) as HV44r; move HV44r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV45l; move HV45l before pvzI11; pose proof (proj2 pvzI11) as HV45r; move HV45r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV46l; move HV46l before pvzI12; pose proof (proj2 pvzI12) as HV46r; move HV46r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV47l; move HV47l before pvzI13; pose proof (proj2 pvzI13) as HV47r; move HV47r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV48l; move HV48l before pvzI14; pose proof (proj2 pvzI14) as HV48r; move HV48r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV49l; move HV49l before pvzI15; pose proof (proj2 pvzI15) as HV49r; move HV49r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV50l; move HV50l before pvzI16; pose proof (proj2 pvzI16) as HV50r; move HV50r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV53l; move HV53l before pvzI18; pose proof (proj2 pvzI18) as HV53r; move HV53r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K7l; move K7l before pvzI20; pose proof (proj2 pvzI20) as K7r; move K7r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K18l; move K18l before pvzI22; pose proof (proj2 pvzI22) as K18r; move K18r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K24l; move K24l before pvzI23; pose proof (proj2 pvzI23) as K24r; move K24r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K32l; move K32l before pvzI24; pose proof (proj2 pvzI24) as K32r; move K32r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K33l; move K33l before pvzI25; pose proof (proj2 pvzI25) as K33r; move K33r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K34l; move K34l before pvzI26; pose proof (proj2 pvzI26) as K34r; move K34r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K41l; move K41l before pvzI27; pose proof (proj2 pvzI27) as K41r; move K41r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K42l; move K42l before pvzI28; pose proof (proj2 pvzI28) as K42r; move K42r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K47l; move K47l before pvzI29; pose proof (proj2 pvzI29) as K47r; move K47r before pvzI29; clear pvzI29.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 52%nat => vz_52 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbstG2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstG2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstG2.kn0).
  { unfold know_ok, PbstG2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear) | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K47l K47r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K70]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstG2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstG2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 240) -> ~ (((vz_40 + 128) + 0) <= bv_unsigned a < ((vz_40 + 128) + 0) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbstG2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstG2.ps0) with 0x7cc28 in Hms. change (SR.ps_regs PbstG2.ps0) with (map (fun i => (i, nth i PbstG2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstG2.ps0) with PbstG2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstG2.regs0 PbstG2.regs_out0 60 KS_bstG2 KS_bstG2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstG2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbstG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbstG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbstG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbstG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbstG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbstG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbstG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG2.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbstG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbstG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbstG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbstG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K41l K41r) | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K33l K33r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K32l K32r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbstG3 := BndP_Eb_059S9.LibSegEb_bstG3.
Definition KS_bstG3 : list nat := Eval vm_compute in (BG.kept_list 60 PbstG3.regs0 PbstG3.regs_out0).
Lemma KS_bstG3_ok : BG.kept_ok 60 PbstG3.regs0 PbstG3.regs_out0 KS_bstG3 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bstG3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 9) = Z_to_bv 64 16 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 19) = Z_to_bv 64 8 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 256) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 256) ->
  4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 16 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  6930432 <= (V 35%nat) <= 140737488355320 -> aligned (V 35%nat) 8 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 8 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 8 <= (V 33%nat)) ->
  0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 18446744073709551615 -> 6930432 <= (V 52%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  L5.u8_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 4096)) -> aligned (V 52%nat) 8 -> L5.u8_at RSEGS M (((V 52%nat) / 8) + 2147450880) 1 ->
  ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 1 <= (V 33%nat)) -> 0 <= (V 53%nat) <= 255 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 256) 32 -> L5KA.zeros_at M ((((V 40%nat) + 256) / 8) + 2147450880) 4 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 256) \/ ((V 40%nat) + 256) + 32 <= 2147446784) -> 4096 <= ((V 40%nat) + 256) <= 140737488355296 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 256) \/ ((V 40%nat) + 256) + 32 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 40%nat) + 256) \/ ((V 40%nat) + 256) + 32 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 256) \/ ((V 40%nat) + 256) + 32 <= (V 34%nat)) -> ((V 35%nat) + 8 <= ((V 40%nat) + 256) \/ ((V 40%nat) + 256) + 32 <= (V 35%nat)) ->
  (65536 + 6864896 <= ((V 40%nat) + 256) \/ ((V 40%nat) + 256) + 32 <= 65536) -> ((V 52%nat) + 1 <= ((V 40%nat) + 256) \/ ((V 40%nat) + 256) + 32 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 770868 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 256) + 0) <= bv_unsigned a < (((V 40%nat) + 256) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 256) + 0) <= i < (((V 40%nat) + 256) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb56a4 M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x KS_bstG3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 698784
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 256)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 256)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 256)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) ((V 2%nat) - 104)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 743392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 771064
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + 288)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 280) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 272) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 264) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 256) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 512)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 40%nat) + 256)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI19 K1 K2 K3 K4 K5 K6 pvzI20 K8 K9 K10 K11 K12 K13 K14 K15 pvzI21 K17 pvzI22 K19 K20 K21 K22 K23 pvzI23 K25 K26 K27 K28 K29 K30 K31 pvzI24 pvzI25 pvzI26 K35 K36 K37 K38 K39 K40 pvzI27 pvzI28 K43 K44 K45 K46 pvzI29 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV43l; move HV43l before pvzI9; pose proof (proj2 pvzI9) as HV43r; move HV43r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV44l; move HV44l before pvzI10; pose proof (proj2 pvzI10) as HV44r; move HV44r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV45l; move HV45l before pvzI11; pose proof (proj2 pvzI11) as HV45r; move HV45r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV46l; move HV46l before pvzI12; pose proof (proj2 pvzI12) as HV46r; move HV46r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV47l; move HV47l before pvzI13; pose proof (proj2 pvzI13) as HV47r; move HV47r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV48l; move HV48l before pvzI14; pose proof (proj2 pvzI14) as HV48r; move HV48r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV49l; move HV49l before pvzI15; pose proof (proj2 pvzI15) as HV49r; move HV49r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV50l; move HV50l before pvzI16; pose proof (proj2 pvzI16) as HV50r; move HV50r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV53l; move HV53l before pvzI18; pose proof (proj2 pvzI18) as HV53r; move HV53r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K7l; move K7l before pvzI20; pose proof (proj2 pvzI20) as K7r; move K7r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K18l; move K18l before pvzI22; pose proof (proj2 pvzI22) as K18r; move K18r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K24l; move K24l before pvzI23; pose proof (proj2 pvzI23) as K24r; move K24r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K32l; move K32l before pvzI24; pose proof (proj2 pvzI24) as K32r; move K32r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K33l; move K33l before pvzI25; pose proof (proj2 pvzI25) as K33r; move K33r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K34l; move K34l before pvzI26; pose proof (proj2 pvzI26) as K34r; move K34r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K41l; move K41l before pvzI27; pose proof (proj2 pvzI27) as K41r; move K41r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K42l; move K42l before pvzI28; pose proof (proj2 pvzI28) as K42r; move K42r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K47l; move K47l before pvzI29; pose proof (proj2 pvzI29) as K47r; move K47r before pvzI29; clear pvzI29.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 52%nat => vz_52 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbstG3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstG3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstG3.kn0).
  { unfold know_ok, PbstG3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear) | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K47l K47r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K70]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstG3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstG3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 240) -> ~ (((vz_40 + 256) + 0) <= bv_unsigned a < ((vz_40 + 256) + 0) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbstG3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstG3.ps0) with 0x7cc28 in Hms. change (SR.ps_regs PbstG3.ps0) with (map (fun i => (i, nth i PbstG3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstG3.ps0) with PbstG3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstG3.regs0 PbstG3.regs_out0 60 KS_bstG3 KS_bstG3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstG3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG3.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbstG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbstG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG3.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbstG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbstG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbstG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG3.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbstG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG3.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbstG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG3.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbstG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG3.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbstG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG3.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbstG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG3.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbstG3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K41l K41r) | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K33l K33r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K32l K32r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbstG4 := BndP_Eb_059S9.LibSegEb_bstG4.
Definition KS_bstG4 : list nat := Eval vm_compute in (BG.kept_list 60 PbstG4.regs0 PbstG4.regs_out0).
Lemma KS_bstG4_ok : BG.kept_ok 60 PbstG4.regs0 PbstG4.regs_out0 KS_bstG4 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bstG4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 9) = Z_to_bv 64 32 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 19) = Z_to_bv 64 16 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 512) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 512) ->
  4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 16 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  6930432 <= (V 35%nat) <= 140737488355320 -> aligned (V 35%nat) 8 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 8 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 8 <= (V 33%nat)) ->
  0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 18446744073709551615 -> 6930432 <= (V 52%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  L5.u8_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 4096)) -> aligned (V 52%nat) 8 -> L5.u8_at RSEGS M (((V 52%nat) / 8) + 2147450880) 1 ->
  ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 1 <= (V 33%nat)) -> 0 <= (V 53%nat) <= 255 -> 4096 <= (V 40%nat) <= 140737488354304 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 512) 32 -> L5KA.zeros_at M ((((V 40%nat) + 512) / 8) + 2147450880) 4 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 512) \/ ((V 40%nat) + 512) + 32 <= 2147446784) -> 4096 <= ((V 40%nat) + 512) <= 140737488355296 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 512) \/ ((V 40%nat) + 512) + 32 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 40%nat) + 512) \/ ((V 40%nat) + 512) + 32 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 512) \/ ((V 40%nat) + 512) + 32 <= (V 34%nat)) -> ((V 35%nat) + 8 <= ((V 40%nat) + 512) \/ ((V 40%nat) + 512) + 32 <= (V 35%nat)) ->
  (65536 + 6864896 <= ((V 40%nat) + 512) \/ ((V 40%nat) + 512) + 32 <= 65536) -> ((V 52%nat) + 1 <= ((V 40%nat) + 512) \/ ((V 40%nat) + 512) + 32 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 770868 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 512) + 0) <= bv_unsigned a < (((V 40%nat) + 512) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 512) + 0) <= i < (((V 40%nat) + 512) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb56a4 M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x KS_bstG4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 698784
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 512)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 512)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 512)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) ((V 2%nat) - 104)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 743392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 771064
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + 544)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 536) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 528) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 520) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 512) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 1024)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 40%nat) + 512)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI19 K1 K2 K3 K4 K5 K6 pvzI20 K8 K9 K10 K11 K12 K13 K14 K15 pvzI21 K17 pvzI22 K19 K20 K21 K22 K23 pvzI23 K25 K26 K27 K28 K29 K30 K31 pvzI24 pvzI25 pvzI26 K35 K36 K37 K38 K39 K40 pvzI27 pvzI28 K43 K44 K45 K46 pvzI29 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV43l; move HV43l before pvzI9; pose proof (proj2 pvzI9) as HV43r; move HV43r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV44l; move HV44l before pvzI10; pose proof (proj2 pvzI10) as HV44r; move HV44r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV45l; move HV45l before pvzI11; pose proof (proj2 pvzI11) as HV45r; move HV45r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV46l; move HV46l before pvzI12; pose proof (proj2 pvzI12) as HV46r; move HV46r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV47l; move HV47l before pvzI13; pose proof (proj2 pvzI13) as HV47r; move HV47r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV48l; move HV48l before pvzI14; pose proof (proj2 pvzI14) as HV48r; move HV48r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV49l; move HV49l before pvzI15; pose proof (proj2 pvzI15) as HV49r; move HV49r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV50l; move HV50l before pvzI16; pose proof (proj2 pvzI16) as HV50r; move HV50r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV53l; move HV53l before pvzI18; pose proof (proj2 pvzI18) as HV53r; move HV53r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K7l; move K7l before pvzI20; pose proof (proj2 pvzI20) as K7r; move K7r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K18l; move K18l before pvzI22; pose proof (proj2 pvzI22) as K18r; move K18r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K24l; move K24l before pvzI23; pose proof (proj2 pvzI23) as K24r; move K24r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K32l; move K32l before pvzI24; pose proof (proj2 pvzI24) as K32r; move K32r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K33l; move K33l before pvzI25; pose proof (proj2 pvzI25) as K33r; move K33r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K34l; move K34l before pvzI26; pose proof (proj2 pvzI26) as K34r; move K34r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K41l; move K41l before pvzI27; pose proof (proj2 pvzI27) as K41r; move K41r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K42l; move K42l before pvzI28; pose proof (proj2 pvzI28) as K42r; move K42r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K47l; move K47l before pvzI29; pose proof (proj2 pvzI29) as K47r; move K47r before pvzI29; clear pvzI29.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 52%nat => vz_52 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbstG4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstG4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstG4.kn0).
  { unfold know_ok, PbstG4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear) | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K47l K47r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K70]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstG4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstG4.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 240) -> ~ (((vz_40 + 512) + 0) <= bv_unsigned a < ((vz_40 + 512) + 0) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbstG4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstG4.ps0) with 0x7cc28 in Hms. change (SR.ps_regs PbstG4.ps0) with (map (fun i => (i, nth i PbstG4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstG4.ps0) with PbstG4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstG4.regs0 PbstG4.regs_out0 60 KS_bstG4 KS_bstG4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstG4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG4.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbstG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG4.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbstG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG4.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbstG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbstG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbstG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG4.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbstG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG4.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbstG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG4.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbstG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG4.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbstG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG4.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbstG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG4.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbstG4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K41l K41r) | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K33l K33r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K32l K32r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbstG5 := BndP_Eb_059S9.LibSegEb_bstG5.
Definition KS_bstG5 : list nat := Eval vm_compute in (BG.kept_list 60 PbstG5.regs0 PbstG5.regs_out0).
Lemma KS_bstG5_ok : BG.kept_ok 60 PbstG5.regs0 PbstG5.regs_out0 KS_bstG5 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bstG5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 9) = Z_to_bv 64 64 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 19) = Z_to_bv 64 32 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 1024) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 1024) ->
  4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 16 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  6930432 <= (V 35%nat) <= 140737488355320 -> aligned (V 35%nat) 8 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 8 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 8 <= (V 33%nat)) ->
  0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 18446744073709551615 -> 6930432 <= (V 52%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  L5.u8_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 4096)) -> aligned (V 52%nat) 8 -> L5.u8_at RSEGS M (((V 52%nat) / 8) + 2147450880) 1 ->
  ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 1 <= (V 33%nat)) -> 0 <= (V 53%nat) <= 255 -> 4096 <= (V 40%nat) <= 140737488353280 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 1024) 32 -> L5KA.zeros_at M ((((V 40%nat) + 1024) / 8) + 2147450880) 4 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 1024) \/ ((V 40%nat) + 1024) + 32 <= 2147446784) -> 4096 <= ((V 40%nat) + 1024) <= 140737488355296 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 1024) \/ ((V 40%nat) + 1024) + 32 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 40%nat) + 1024) \/ ((V 40%nat) + 1024) + 32 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 1024) \/ ((V 40%nat) + 1024) + 32 <= (V 34%nat)) -> ((V 35%nat) + 8 <= ((V 40%nat) + 1024) \/ ((V 40%nat) + 1024) + 32 <= (V 35%nat)) ->
  (65536 + 6864896 <= ((V 40%nat) + 1024) \/ ((V 40%nat) + 1024) + 32 <= 65536) -> ((V 52%nat) + 1 <= ((V 40%nat) + 1024) \/ ((V 40%nat) + 1024) + 32 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 770868 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 1024) + 0) <= bv_unsigned a < (((V 40%nat) + 1024) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 1024) + 0) <= i < (((V 40%nat) + 1024) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb56a4 M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x KS_bstG5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 698784
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 1024)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 1024)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 1024)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) ((V 2%nat) - 104)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 743392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 771064
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + 1056)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 1048) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 1040) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 1032) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 1024) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 2048)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 40%nat) + 1024)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI19 K1 K2 K3 K4 K5 K6 pvzI20 K8 K9 K10 K11 K12 K13 K14 K15 pvzI21 K17 pvzI22 K19 K20 K21 K22 K23 pvzI23 K25 K26 K27 K28 K29 K30 K31 pvzI24 pvzI25 pvzI26 K35 K36 K37 K38 K39 K40 pvzI27 pvzI28 K43 K44 K45 K46 pvzI29 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV43l; move HV43l before pvzI9; pose proof (proj2 pvzI9) as HV43r; move HV43r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV44l; move HV44l before pvzI10; pose proof (proj2 pvzI10) as HV44r; move HV44r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV45l; move HV45l before pvzI11; pose proof (proj2 pvzI11) as HV45r; move HV45r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV46l; move HV46l before pvzI12; pose proof (proj2 pvzI12) as HV46r; move HV46r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV47l; move HV47l before pvzI13; pose proof (proj2 pvzI13) as HV47r; move HV47r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV48l; move HV48l before pvzI14; pose proof (proj2 pvzI14) as HV48r; move HV48r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV49l; move HV49l before pvzI15; pose proof (proj2 pvzI15) as HV49r; move HV49r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV50l; move HV50l before pvzI16; pose proof (proj2 pvzI16) as HV50r; move HV50r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV53l; move HV53l before pvzI18; pose proof (proj2 pvzI18) as HV53r; move HV53r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K7l; move K7l before pvzI20; pose proof (proj2 pvzI20) as K7r; move K7r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K18l; move K18l before pvzI22; pose proof (proj2 pvzI22) as K18r; move K18r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K24l; move K24l before pvzI23; pose proof (proj2 pvzI23) as K24r; move K24r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K32l; move K32l before pvzI24; pose proof (proj2 pvzI24) as K32r; move K32r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K33l; move K33l before pvzI25; pose proof (proj2 pvzI25) as K33r; move K33r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K34l; move K34l before pvzI26; pose proof (proj2 pvzI26) as K34r; move K34r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K41l; move K41l before pvzI27; pose proof (proj2 pvzI27) as K41r; move K41r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K42l; move K42l before pvzI28; pose proof (proj2 pvzI28) as K42r; move K42r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K47l; move K47l before pvzI29; pose proof (proj2 pvzI29) as K47r; move K47r before pvzI29; clear pvzI29.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 52%nat => vz_52 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbstG5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstG5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstG5.kn0).
  { unfold know_ok, PbstG5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear) | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K47l K47r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K70]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstG5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstG5.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 240) -> ~ (((vz_40 + 1024) + 0) <= bv_unsigned a < ((vz_40 + 1024) + 0) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbstG5.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstG5.ps0) with 0x7cc28 in Hms. change (SR.ps_regs PbstG5.ps0) with (map (fun i => (i, nth i PbstG5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstG5.ps0) with PbstG5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstG5.regs0 PbstG5.regs_out0 60 KS_bstG5 KS_bstG5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstG5.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG5.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbstG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG5.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbstG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG5.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbstG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbstG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG5.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbstG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG5.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbstG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG5.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbstG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG5.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbstG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG5.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbstG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG5.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbstG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG5.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbstG5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K41l K41r) | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K33l K33r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K32l K32r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbstG6 := BndP_Eb_059S9.LibSegEb_bstG6.
Definition KS_bstG6 : list nat := Eval vm_compute in (BG.kept_list 60 PbstG6.regs0 PbstG6.regs_out0).
Lemma KS_bstG6_ok : BG.kept_ok 60 PbstG6.regs0 PbstG6.regs_out0 KS_bstG6 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bstG6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 9) = Z_to_bv 64 128 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 19) = Z_to_bv 64 64 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 2048) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 2048) ->
  4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 16 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  6930432 <= (V 35%nat) <= 140737488355320 -> aligned (V 35%nat) 8 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 8 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 8 <= (V 33%nat)) ->
  0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 18446744073709551615 -> 6930432 <= (V 52%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  L5.u8_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 4096)) -> aligned (V 52%nat) 8 -> L5.u8_at RSEGS M (((V 52%nat) / 8) + 2147450880) 1 ->
  ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 1 <= (V 33%nat)) -> 0 <= (V 53%nat) <= 255 -> 4096 <= (V 40%nat) <= 140737488351232 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 2048) 32 -> L5KA.zeros_at M ((((V 40%nat) + 2048) / 8) + 2147450880) 4 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 2048) \/ ((V 40%nat) + 2048) + 32 <= 2147446784) -> 4096 <= ((V 40%nat) + 2048) <= 140737488355296 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 2048) \/ ((V 40%nat) + 2048) + 32 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 40%nat) + 2048) \/ ((V 40%nat) + 2048) + 32 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 2048) \/ ((V 40%nat) + 2048) + 32 <= (V 34%nat)) -> ((V 35%nat) + 8 <= ((V 40%nat) + 2048) \/ ((V 40%nat) + 2048) + 32 <= (V 35%nat)) ->
  (65536 + 6864896 <= ((V 40%nat) + 2048) \/ ((V 40%nat) + 2048) + 32 <= 65536) -> ((V 52%nat) + 1 <= ((V 40%nat) + 2048) \/ ((V 40%nat) + 2048) + 32 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 770868 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 2048) + 0) <= bv_unsigned a < (((V 40%nat) + 2048) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 2048) + 0) <= i < (((V 40%nat) + 2048) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb56a4 M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x KS_bstG6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 698784
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 2048)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 2048)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 2048)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) ((V 2%nat) - 104)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 743392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 771064
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + 2080)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 2072) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 2064) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 2056) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 2048) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 4096)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 40%nat) + 2048)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI19 K1 K2 K3 K4 K5 K6 pvzI20 K8 K9 K10 K11 K12 K13 K14 K15 pvzI21 K17 pvzI22 K19 K20 K21 K22 K23 pvzI23 K25 K26 K27 K28 K29 K30 K31 pvzI24 pvzI25 pvzI26 K35 K36 K37 K38 K39 K40 pvzI27 pvzI28 K43 K44 K45 K46 pvzI29 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV43l; move HV43l before pvzI9; pose proof (proj2 pvzI9) as HV43r; move HV43r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV44l; move HV44l before pvzI10; pose proof (proj2 pvzI10) as HV44r; move HV44r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV45l; move HV45l before pvzI11; pose proof (proj2 pvzI11) as HV45r; move HV45r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV46l; move HV46l before pvzI12; pose proof (proj2 pvzI12) as HV46r; move HV46r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV47l; move HV47l before pvzI13; pose proof (proj2 pvzI13) as HV47r; move HV47r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV48l; move HV48l before pvzI14; pose proof (proj2 pvzI14) as HV48r; move HV48r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV49l; move HV49l before pvzI15; pose proof (proj2 pvzI15) as HV49r; move HV49r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV50l; move HV50l before pvzI16; pose proof (proj2 pvzI16) as HV50r; move HV50r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV53l; move HV53l before pvzI18; pose proof (proj2 pvzI18) as HV53r; move HV53r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K7l; move K7l before pvzI20; pose proof (proj2 pvzI20) as K7r; move K7r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K18l; move K18l before pvzI22; pose proof (proj2 pvzI22) as K18r; move K18r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K24l; move K24l before pvzI23; pose proof (proj2 pvzI23) as K24r; move K24r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K32l; move K32l before pvzI24; pose proof (proj2 pvzI24) as K32r; move K32r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K33l; move K33l before pvzI25; pose proof (proj2 pvzI25) as K33r; move K33r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K34l; move K34l before pvzI26; pose proof (proj2 pvzI26) as K34r; move K34r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K41l; move K41l before pvzI27; pose proof (proj2 pvzI27) as K41r; move K41r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K42l; move K42l before pvzI28; pose proof (proj2 pvzI28) as K42r; move K42r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K47l; move K47l before pvzI29; pose proof (proj2 pvzI29) as K47r; move K47r before pvzI29; clear pvzI29.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 52%nat => vz_52 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbstG6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstG6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstG6.kn0).
  { unfold know_ok, PbstG6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear) | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K47l K47r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K70]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstG6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstG6.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 240) -> ~ (((vz_40 + 2048) + 0) <= bv_unsigned a < ((vz_40 + 2048) + 0) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbstG6.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstG6.ps0) with 0x7cc28 in Hms. change (SR.ps_regs PbstG6.ps0) with (map (fun i => (i, nth i PbstG6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstG6.ps0) with PbstG6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstG6.regs0 PbstG6.regs_out0 60 KS_bstG6 KS_bstG6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstG6.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG6.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbstG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG6.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbstG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG6.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbstG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG6.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbstG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG6.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbstG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG6.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbstG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG6.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbstG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG6.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbstG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG6.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbstG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG6.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbstG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG6.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbstG6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K41l K41r) | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K33l K33r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K32l K32r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbstG7 := BndP_Eb_059S9.LibSegEb_bstG7.
Definition KS_bstG7 : list nat := Eval vm_compute in (BG.kept_list 60 PbstG7.regs0 PbstG7.regs_out0).
Lemma KS_bstG7_ok : BG.kept_ok 60 PbstG7.regs0 PbstG7.regs_out0 KS_bstG7 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bstG7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 9) = Z_to_bv 64 256 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 19) = Z_to_bv 64 128 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 4096) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 4096) ->
  4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 16 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  6930432 <= (V 35%nat) <= 140737488355320 -> aligned (V 35%nat) 8 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 8 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 8 <= (V 33%nat)) ->
  0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 18446744073709551615 -> 6930432 <= (V 52%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  L5.u8_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 4096)) -> aligned (V 52%nat) 8 -> L5.u8_at RSEGS M (((V 52%nat) / 8) + 2147450880) 1 ->
  ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 1 <= (V 33%nat)) -> 0 <= (V 53%nat) <= 255 -> 4096 <= (V 40%nat) <= 140737488347136 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 4096) 32 -> L5KA.zeros_at M ((((V 40%nat) + 4096) / 8) + 2147450880) 4 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 4096) \/ ((V 40%nat) + 4096) + 32 <= 2147446784) -> 4096 <= ((V 40%nat) + 4096) <= 140737488355296 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 4096) \/ ((V 40%nat) + 4096) + 32 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 40%nat) + 4096) \/ ((V 40%nat) + 4096) + 32 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 4096) \/ ((V 40%nat) + 4096) + 32 <= (V 34%nat)) -> ((V 35%nat) + 8 <= ((V 40%nat) + 4096) \/ ((V 40%nat) + 4096) + 32 <= (V 35%nat)) ->
  (65536 + 6864896 <= ((V 40%nat) + 4096) \/ ((V 40%nat) + 4096) + 32 <= 65536) -> ((V 52%nat) + 1 <= ((V 40%nat) + 4096) \/ ((V 40%nat) + 4096) + 32 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 770868 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 4096) + 0) <= bv_unsigned a < (((V 40%nat) + 4096) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 4096) + 0) <= i < (((V 40%nat) + 4096) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb56a4 M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x KS_bstG7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 698784
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 4096)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 4096)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 4096)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) ((V 2%nat) - 104)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 743392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 771064
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + 4128)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 4120) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 4112) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 4104) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 4096) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 8192)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 40%nat) + 4096)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI19 K1 K2 K3 K4 K5 K6 pvzI20 K8 K9 K10 K11 K12 K13 K14 K15 pvzI21 K17 pvzI22 K19 K20 K21 K22 K23 pvzI23 K25 K26 K27 K28 K29 K30 K31 pvzI24 pvzI25 pvzI26 K35 K36 K37 K38 K39 K40 pvzI27 pvzI28 K43 K44 K45 K46 pvzI29 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV43l; move HV43l before pvzI9; pose proof (proj2 pvzI9) as HV43r; move HV43r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV44l; move HV44l before pvzI10; pose proof (proj2 pvzI10) as HV44r; move HV44r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV45l; move HV45l before pvzI11; pose proof (proj2 pvzI11) as HV45r; move HV45r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV46l; move HV46l before pvzI12; pose proof (proj2 pvzI12) as HV46r; move HV46r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV47l; move HV47l before pvzI13; pose proof (proj2 pvzI13) as HV47r; move HV47r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV48l; move HV48l before pvzI14; pose proof (proj2 pvzI14) as HV48r; move HV48r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV49l; move HV49l before pvzI15; pose proof (proj2 pvzI15) as HV49r; move HV49r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV50l; move HV50l before pvzI16; pose proof (proj2 pvzI16) as HV50r; move HV50r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV53l; move HV53l before pvzI18; pose proof (proj2 pvzI18) as HV53r; move HV53r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K7l; move K7l before pvzI20; pose proof (proj2 pvzI20) as K7r; move K7r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K18l; move K18l before pvzI22; pose proof (proj2 pvzI22) as K18r; move K18r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K24l; move K24l before pvzI23; pose proof (proj2 pvzI23) as K24r; move K24r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K32l; move K32l before pvzI24; pose proof (proj2 pvzI24) as K32r; move K32r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K33l; move K33l before pvzI25; pose proof (proj2 pvzI25) as K33r; move K33r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K34l; move K34l before pvzI26; pose proof (proj2 pvzI26) as K34r; move K34r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K41l; move K41l before pvzI27; pose proof (proj2 pvzI27) as K41r; move K41r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K42l; move K42l before pvzI28; pose proof (proj2 pvzI28) as K42r; move K42r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K47l; move K47l before pvzI29; pose proof (proj2 pvzI29) as K47r; move K47r before pvzI29; clear pvzI29.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 52%nat => vz_52 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbstG7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstG7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstG7.kn0).
  { unfold know_ok, PbstG7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear) | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K47l K47r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K70]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstG7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstG7.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 240) -> ~ (((vz_40 + 4096) + 0) <= bv_unsigned a < ((vz_40 + 4096) + 0) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbstG7.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstG7.ps0) with 0x7cc28 in Hms. change (SR.ps_regs PbstG7.ps0) with (map (fun i => (i, nth i PbstG7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstG7.ps0) with PbstG7.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstG7.regs0 PbstG7.regs_out0 60 KS_bstG7 KS_bstG7_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstG7.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG7.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbstG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG7.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbstG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG7.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbstG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG7.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbstG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG7.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbstG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG7.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbstG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG7.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbstG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG7.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbstG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG7.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbstG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG7.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbstG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG7.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbstG7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K41l K41r) | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K33l K33r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K32l K32r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbstG8 := BndP_Eb_059S9.LibSegEb_bstG8.
Definition KS_bstG8 : list nat := Eval vm_compute in (BG.kept_list 60 PbstG8.regs0 PbstG8.regs_out0).
Lemma KS_bstG8_ok : BG.kept_ok 60 PbstG8.regs0 PbstG8.regs_out0 KS_bstG8 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bstG8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 9) = Z_to_bv 64 512 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 19) = Z_to_bv 64 256 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 8192) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 8192) ->
  4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 16 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  6930432 <= (V 35%nat) <= 140737488355320 -> aligned (V 35%nat) 8 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 8 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 8 <= (V 33%nat)) ->
  0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 18446744073709551615 -> 6930432 <= (V 52%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  L5.u8_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 4096)) -> aligned (V 52%nat) 8 -> L5.u8_at RSEGS M (((V 52%nat) / 8) + 2147450880) 1 ->
  ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 1 <= (V 33%nat)) -> 0 <= (V 53%nat) <= 255 -> 4096 <= (V 40%nat) <= 140737488338944 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 8192) 32 -> L5KA.zeros_at M ((((V 40%nat) + 8192) / 8) + 2147450880) 4 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 8192) \/ ((V 40%nat) + 8192) + 32 <= 2147446784) -> 4096 <= ((V 40%nat) + 8192) <= 140737488355296 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 8192) \/ ((V 40%nat) + 8192) + 32 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 40%nat) + 8192) \/ ((V 40%nat) + 8192) + 32 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 8192) \/ ((V 40%nat) + 8192) + 32 <= (V 34%nat)) -> ((V 35%nat) + 8 <= ((V 40%nat) + 8192) \/ ((V 40%nat) + 8192) + 32 <= (V 35%nat)) ->
  (65536 + 6864896 <= ((V 40%nat) + 8192) \/ ((V 40%nat) + 8192) + 32 <= 65536) -> ((V 52%nat) + 1 <= ((V 40%nat) + 8192) \/ ((V 40%nat) + 8192) + 32 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 770868 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 8192) + 0) <= bv_unsigned a < (((V 40%nat) + 8192) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 8192) + 0) <= i < (((V 40%nat) + 8192) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb56a4 M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x KS_bstG8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 698784
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 8192)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 8192)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 8192)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) ((V 2%nat) - 104)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 743392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 771064
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + 8224)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 8216) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 8208) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 8200) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 8192) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 16384)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 40%nat) + 8192)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI19 K1 K2 K3 K4 K5 K6 pvzI20 K8 K9 K10 K11 K12 K13 K14 K15 pvzI21 K17 pvzI22 K19 K20 K21 K22 K23 pvzI23 K25 K26 K27 K28 K29 K30 K31 pvzI24 pvzI25 pvzI26 K35 K36 K37 K38 K39 K40 pvzI27 pvzI28 K43 K44 K45 K46 pvzI29 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV43l; move HV43l before pvzI9; pose proof (proj2 pvzI9) as HV43r; move HV43r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV44l; move HV44l before pvzI10; pose proof (proj2 pvzI10) as HV44r; move HV44r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV45l; move HV45l before pvzI11; pose proof (proj2 pvzI11) as HV45r; move HV45r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV46l; move HV46l before pvzI12; pose proof (proj2 pvzI12) as HV46r; move HV46r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV47l; move HV47l before pvzI13; pose proof (proj2 pvzI13) as HV47r; move HV47r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV48l; move HV48l before pvzI14; pose proof (proj2 pvzI14) as HV48r; move HV48r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV49l; move HV49l before pvzI15; pose proof (proj2 pvzI15) as HV49r; move HV49r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV50l; move HV50l before pvzI16; pose proof (proj2 pvzI16) as HV50r; move HV50r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV53l; move HV53l before pvzI18; pose proof (proj2 pvzI18) as HV53r; move HV53r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K7l; move K7l before pvzI20; pose proof (proj2 pvzI20) as K7r; move K7r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K18l; move K18l before pvzI22; pose proof (proj2 pvzI22) as K18r; move K18r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K24l; move K24l before pvzI23; pose proof (proj2 pvzI23) as K24r; move K24r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K32l; move K32l before pvzI24; pose proof (proj2 pvzI24) as K32r; move K32r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K33l; move K33l before pvzI25; pose proof (proj2 pvzI25) as K33r; move K33r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K34l; move K34l before pvzI26; pose proof (proj2 pvzI26) as K34r; move K34r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K41l; move K41l before pvzI27; pose proof (proj2 pvzI27) as K41r; move K41r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K42l; move K42l before pvzI28; pose proof (proj2 pvzI28) as K42r; move K42r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K47l; move K47l before pvzI29; pose proof (proj2 pvzI29) as K47r; move K47r before pvzI29; clear pvzI29.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 52%nat => vz_52 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbstG8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstG8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstG8.kn0).
  { unfold know_ok, PbstG8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear) | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K47l K47r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K70]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstG8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstG8.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 240) -> ~ (((vz_40 + 8192) + 0) <= bv_unsigned a < ((vz_40 + 8192) + 0) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbstG8.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstG8.ps0) with 0x7cc28 in Hms. change (SR.ps_regs PbstG8.ps0) with (map (fun i => (i, nth i PbstG8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstG8.ps0) with PbstG8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstG8.regs0 PbstG8.regs_out0 60 KS_bstG8 KS_bstG8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstG8.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG8.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbstG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG8.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbstG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG8.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbstG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG8.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbstG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG8.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbstG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG8.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbstG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG8.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbstG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG8.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbstG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG8.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbstG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG8.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbstG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG8.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbstG8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K41l K41r) | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K33l K33r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K32l K32r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbstG9 := BndP_Eb_059S9.LibSegEb_bstG9.
Definition KS_bstG9 : list nat := Eval vm_compute in (BG.kept_list 60 PbstG9.regs0 PbstG9.regs_out0).
Lemma KS_bstG9_ok : BG.kept_ok 60 PbstG9.regs0 PbstG9.regs_out0 KS_bstG9 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bstG9_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 9) = Z_to_bv 64 1024 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 19) = Z_to_bv 64 512 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 16384) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 16384) ->
  4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 16 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  6930432 <= (V 35%nat) <= 140737488355320 -> aligned (V 35%nat) 8 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 8 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 8 <= (V 33%nat)) ->
  0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 18446744073709551615 -> 6930432 <= (V 52%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  L5.u8_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 4096)) -> aligned (V 52%nat) 8 -> L5.u8_at RSEGS M (((V 52%nat) / 8) + 2147450880) 1 ->
  ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 1 <= (V 33%nat)) -> 0 <= (V 53%nat) <= 255 -> 4096 <= (V 40%nat) <= 140737488322560 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 16384) 32 -> L5KA.zeros_at M ((((V 40%nat) + 16384) / 8) + 2147450880) 4 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 16384) \/ ((V 40%nat) + 16384) + 32 <= 2147446784) -> 4096 <= ((V 40%nat) + 16384) <= 140737488355296 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 16384) \/ ((V 40%nat) + 16384) + 32 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 40%nat) + 16384) \/ ((V 40%nat) + 16384) + 32 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 16384) \/ ((V 40%nat) + 16384) + 32 <= (V 34%nat)) -> ((V 35%nat) + 8 <= ((V 40%nat) + 16384) \/ ((V 40%nat) + 16384) + 32 <= (V 35%nat)) ->
  (65536 + 6864896 <= ((V 40%nat) + 16384) \/ ((V 40%nat) + 16384) + 32 <= 65536) -> ((V 52%nat) + 1 <= ((V 40%nat) + 16384) \/ ((V 40%nat) + 16384) + 32 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 770868 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 16384) + 0) <= bv_unsigned a < (((V 40%nat) + 16384) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 16384) + 0) <= i < (((V 40%nat) + 16384) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb56a4 M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x KS_bstG9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 698784
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 16384)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 16384)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 16384)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) ((V 2%nat) - 104)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 743392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 771064
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + 16416)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 16408) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 16400) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 16392) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 16384) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 32768)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 40%nat) + 16384)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI19 K1 K2 K3 K4 K5 K6 pvzI20 K8 K9 K10 K11 K12 K13 K14 K15 pvzI21 K17 pvzI22 K19 K20 K21 K22 K23 pvzI23 K25 K26 K27 K28 K29 K30 K31 pvzI24 pvzI25 pvzI26 K35 K36 K37 K38 K39 K40 pvzI27 pvzI28 K43 K44 K45 K46 pvzI29 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV43l; move HV43l before pvzI9; pose proof (proj2 pvzI9) as HV43r; move HV43r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV44l; move HV44l before pvzI10; pose proof (proj2 pvzI10) as HV44r; move HV44r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV45l; move HV45l before pvzI11; pose proof (proj2 pvzI11) as HV45r; move HV45r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV46l; move HV46l before pvzI12; pose proof (proj2 pvzI12) as HV46r; move HV46r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV47l; move HV47l before pvzI13; pose proof (proj2 pvzI13) as HV47r; move HV47r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV48l; move HV48l before pvzI14; pose proof (proj2 pvzI14) as HV48r; move HV48r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV49l; move HV49l before pvzI15; pose proof (proj2 pvzI15) as HV49r; move HV49r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV50l; move HV50l before pvzI16; pose proof (proj2 pvzI16) as HV50r; move HV50r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV53l; move HV53l before pvzI18; pose proof (proj2 pvzI18) as HV53r; move HV53r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K7l; move K7l before pvzI20; pose proof (proj2 pvzI20) as K7r; move K7r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K18l; move K18l before pvzI22; pose proof (proj2 pvzI22) as K18r; move K18r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K24l; move K24l before pvzI23; pose proof (proj2 pvzI23) as K24r; move K24r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K32l; move K32l before pvzI24; pose proof (proj2 pvzI24) as K32r; move K32r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K33l; move K33l before pvzI25; pose proof (proj2 pvzI25) as K33r; move K33r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K34l; move K34l before pvzI26; pose proof (proj2 pvzI26) as K34r; move K34r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K41l; move K41l before pvzI27; pose proof (proj2 pvzI27) as K41r; move K41r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K42l; move K42l before pvzI28; pose proof (proj2 pvzI28) as K42r; move K42r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K47l; move K47l before pvzI29; pose proof (proj2 pvzI29) as K47r; move K47r before pvzI29; clear pvzI29.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 52%nat => vz_52 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbstG9.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstG9.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstG9.kn0).
  { unfold know_ok, PbstG9.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear) | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K47l K47r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K70]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstG9.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstG9.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 240) -> ~ (((vz_40 + 16384) + 0) <= bv_unsigned a < ((vz_40 + 16384) + 0) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbstG9.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstG9.ps0) with 0x7cc28 in Hms. change (SR.ps_regs PbstG9.ps0) with (map (fun i => (i, nth i PbstG9.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstG9.ps0) with PbstG9.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstG9.regs0 PbstG9.regs_out0 60 KS_bstG9 KS_bstG9_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstG9.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG9.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbstG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG9.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbstG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG9.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbstG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG9.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG9.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG9.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbstG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG9.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbstG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG9.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbstG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG9.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbstG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG9.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbstG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG9.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbstG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG9.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbstG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG9.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbstG9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K41l K41r) | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K33l K33r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K32l K32r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module PbstG10 := BndP_Eb_059S9.LibSegEb_bstG10.
Definition KS_bstG10 : list nat := Eval vm_compute in (BG.kept_list 60 PbstG10.regs0 PbstG10.regs_out0).
Lemma KS_bstG10_ok : BG.kept_ok 60 PbstG10.regs0 PbstG10.regs_out0 KS_bstG10 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bstG10_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 9) = Z_to_bv 64 2048 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 19) = Z_to_bv 64 1024 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2147450880 ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 6930432 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6864896 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + 32768) -> L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 36%nat) + 32768) ->
  4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 16 -> 6930432 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) ->
  6930432 <= (V 35%nat) <= 140737488355320 -> aligned (V 35%nat) 8 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 8 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 8 <= (V 33%nat)) ->
  0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 18446744073709551615 -> 6930432 <= (V 52%nat) <= 140737488355327 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  L5.u8_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 4096)) -> aligned (V 52%nat) 8 -> L5.u8_at RSEGS M (((V 52%nat) / 8) + 2147450880) 1 ->
  ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 1 <= (V 33%nat)) -> 0 <= (V 53%nat) <= 255 -> 4096 <= (V 40%nat) <= 140737488289792 -> aligned (V 40%nat) 16 ->
  L5.writable RSEGS M ((V 40%nat) + 32768) 32 -> L5KA.zeros_at M ((((V 40%nat) + 32768) / 8) + 2147450880) 4 -> (2147446784 + 17592186048512 <= ((V 40%nat) + 32768) \/ ((V 40%nat) + 32768) + 32 <= 2147446784) -> 4096 <= ((V 40%nat) + 32768) <= 140737488355296 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 40%nat) + 32768) \/ ((V 40%nat) + 32768) + 32 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 40%nat) + 32768) \/ ((V 40%nat) + 32768) + 32 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 40%nat) + 32768) \/ ((V 40%nat) + 32768) + 32 <= (V 34%nat)) -> ((V 35%nat) + 8 <= ((V 40%nat) + 32768) \/ ((V 40%nat) + 32768) + 32 <= (V 35%nat)) ->
  (65536 + 6864896 <= ((V 40%nat) + 32768) \/ ((V 40%nat) + 32768) + 32 <= 65536) -> ((V 52%nat) + 1 <= ((V 40%nat) + 32768) \/ ((V 40%nat) + 32768) + 32 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 770868 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 32768) + 0) <= bv_unsigned a < (((V 40%nat) + 32768) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 240) -> ~ ((((V 40%nat) + 32768) + 0) <= i < (((V 40%nat) + 32768) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb56a4 M) (st fx' R' 0x7cc28 M')
        /\ (forall x, In x KS_bstG10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 698784
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 208)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 32768)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + 32768)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 32768)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) ((V 2%nat) - 104)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) 743392
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 771064
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + 32800)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 32792) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 32784) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 32776) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 40%nat) + 32768) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 65536)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 40%nat) + 32768)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G10 G18 G19 G20 G21 G22 pvzI19 K1 K2 K3 K4 K5 K6 pvzI20 K8 K9 K10 K11 K12 K13 K14 K15 pvzI21 K17 pvzI22 K19 K20 K21 K22 K23 pvzI23 K25 K26 K27 K28 K29 K30 K31 pvzI24 pvzI25 pvzI26 K35 K36 K37 K38 K39 K40 pvzI27 pvzI28 K43 K44 K45 K46 pvzI29 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV39l; move HV39l before pvzI7; pose proof (proj2 pvzI7) as HV39r; move HV39r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV40l; move HV40l before pvzI8; pose proof (proj2 pvzI8) as HV40r; move HV40r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV43l; move HV43l before pvzI9; pose proof (proj2 pvzI9) as HV43r; move HV43r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV44l; move HV44l before pvzI10; pose proof (proj2 pvzI10) as HV44r; move HV44r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV45l; move HV45l before pvzI11; pose proof (proj2 pvzI11) as HV45r; move HV45r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV46l; move HV46l before pvzI12; pose proof (proj2 pvzI12) as HV46r; move HV46r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV47l; move HV47l before pvzI13; pose proof (proj2 pvzI13) as HV47r; move HV47r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV48l; move HV48l before pvzI14; pose proof (proj2 pvzI14) as HV48r; move HV48r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV49l; move HV49l before pvzI15; pose proof (proj2 pvzI15) as HV49r; move HV49r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV50l; move HV50l before pvzI16; pose proof (proj2 pvzI16) as HV50r; move HV50r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV52l; move HV52l before pvzI17; pose proof (proj2 pvzI17) as HV52r; move HV52r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV53l; move HV53l before pvzI18; pose proof (proj2 pvzI18) as HV53r; move HV53r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K0l; move K0l before pvzI19; pose proof (proj2 pvzI19) as K0r; move K0r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K7l; move K7l before pvzI20; pose proof (proj2 pvzI20) as K7r; move K7r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K16l; move K16l before pvzI21; pose proof (proj2 pvzI21) as K16r; move K16r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K18l; move K18l before pvzI22; pose proof (proj2 pvzI22) as K18r; move K18r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K24l; move K24l before pvzI23; pose proof (proj2 pvzI23) as K24r; move K24r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K32l; move K32l before pvzI24; pose proof (proj2 pvzI24) as K32r; move K32r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K33l; move K33l before pvzI25; pose proof (proj2 pvzI25) as K33r; move K33r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K34l; move K34l before pvzI26; pose proof (proj2 pvzI26) as K34r; move K34r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K41l; move K41l before pvzI27; pose proof (proj2 pvzI27) as K41r; move K41r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K42l; move K42l before pvzI28; pose proof (proj2 pvzI28) as K42r; move K42r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K47l; move K47l before pvzI29; pose proof (proj2 pvzI29) as K47r; move K47r before pvzI29; clear pvzI29.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 52%nat => vz_52 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbstG10.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbstG10.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbstG10.kn0).
  { unfold know_ok, PbstG10.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K2]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K16l K16r) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | clear - HV34l HV34r K18l K18r K20 K23 K30 K50; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | clear - HV35l HV35r K24l K24r K26 K29 K31 K51; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | clear - HV52l HV52r K34l K34r K35 K37 K40 K53; lia | byte_tac ltac:(clear) | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K44]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | exact (conj K47l K47r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk ZA ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48; lia | exactA K70]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbstG10.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbstG10.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 240) -> ~ (((vz_40 + 32768) + 0) <= bv_unsigned a < ((vz_40 + 32768) + 0) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbstG10.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbstG10.ps0) with 0x7cc28 in Hms. change (SR.ps_regs PbstG10.ps0) with (map (fun i => (i, nth i PbstG10.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbstG10.ps0) with PbstG10.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbstG10.regs0 PbstG10.regs_out0 60 KS_bstG10 KS_bstG10_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbstG10.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbstG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG10.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbstG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG10.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbstG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG10.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbstG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG10.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbstG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG10.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbstG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG10.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbstG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG10.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbstG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG10.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbstG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG10.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbstG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG10.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbstG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG10.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbstG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG10.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbstG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbstG10.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbstG10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K18l K18r K20 K23 K30 K50) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K24l K24r K26 K29 K31 K51) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV52l HV52r K34l K34r K35 K37 K40 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K41l K41r) | byte_tac ltac:(clear - HV53l HV53r K41l K41r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K33l K33r) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K32l K32r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K42l K42r K46 K47l K47r K48 K49 K50 K51 K52 K53) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV43l HV43r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV44l HV44r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV45l HV45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV46l HV46r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV47l HV47r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K23 K29 K37 K48) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K7l K7r K9 K11 K12 K30 K31 K40 K49) | clear; lia].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

End PMBSLTP3.
