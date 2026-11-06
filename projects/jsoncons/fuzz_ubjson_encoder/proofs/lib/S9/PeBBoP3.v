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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_012S9 BndP_Eb_013S9 BndP_Eb_014S9 BndP_Eb_015S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBBOP3.
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

Module PbboCTr := BndP_Eb_012S9.LibSegEb_bboCTr.
Definition KS_bboCTr : list nat := Eval vm_compute in (BG.kept_list 72 PbboCTr.regs0 PbboCTr.regs_out0).
Lemma KS_bboCTr_ok : BG.kept_ok 72 PbboCTr.regs0 PbboCTr.regs_out0 KS_bboCTr = true. Proof. vm_compute. reflexivity. Qed.
Lemma bboCTr_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 36%nat) + 368) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 368) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 192)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 192) + 192 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 192)) ->
  6930432 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6930432 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 192) + 192 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1204292 <= (V 47%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 37%nat) -> L5.u64_at RSEGS M (V 37%nat) 1277312 -> L5KA.zeros_at M 2147610552 1 ->
  L5KA.zeros_at M 2147610553 1 -> L5.u8_at RSEGS M ((V 36%nat) + 16) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 50%nat) -> 0 <= (V 50%nat) <= 16777216 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbb95c M) (st fx' R' 0xbba38 M')
        /\ (forall x, In x KS_bboCTr -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 69%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 1
        /\ L5.defined M' ((V 47%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 G2 G8 G9 G18 G19 G20 G22 G23 G25 G26 G27 K0 K1 K2 pvzI21 K4 K5 pvzI22 K7 K8 K9 K10 K11 K12 K13 pvzI23 K15 K16 K17 K18 K19 pvzI24 K21 K22 K23 K24 K25 K26 K27 K28 pvzI25 K30 K31 K32 K33 K34 K35 pvzI26 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70 pvzI27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV58l; move HV58l before pvzI9; pose proof (proj2 pvzI9) as HV58r; move HV58r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV59l; move HV59l before pvzI10; pose proof (proj2 pvzI10) as HV59r; move HV59r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV60l; move HV60l before pvzI11; pose proof (proj2 pvzI11) as HV60r; move HV60r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV61l; move HV61l before pvzI12; pose proof (proj2 pvzI12) as HV61r; move HV61r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV62l; move HV62l before pvzI13; pose proof (proj2 pvzI13) as HV62r; move HV62r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV63l; move HV63l before pvzI14; pose proof (proj2 pvzI14) as HV63r; move HV63r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV64l; move HV64l before pvzI15; pose proof (proj2 pvzI15) as HV64r; move HV64r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV65l; move HV65l before pvzI16; pose proof (proj2 pvzI16) as HV65r; move HV65r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV66l; move HV66l before pvzI17; pose proof (proj2 pvzI17) as HV66r; move HV66r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV67l; move HV67l before pvzI18; pose proof (proj2 pvzI18) as HV67r; move HV67r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV68l; move HV68l before pvzI19; pose proof (proj2 pvzI19) as HV68r; move HV68r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV69l; move HV69l before pvzI20; pose proof (proj2 pvzI20) as HV69r; move HV69r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K3l; move K3l before pvzI21; pose proof (proj2 pvzI21) as K3r; move K3r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K6l; move K6l before pvzI22; pose proof (proj2 pvzI22) as K6r; move K6r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K14l; move K14l before pvzI23; pose proof (proj2 pvzI23) as K14r; move K14r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K20l; move K20l before pvzI24; pose proof (proj2 pvzI24) as K20r; move K20r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K29l; move K29l before pvzI25; pose proof (proj2 pvzI25) as K29r; move K29r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K36l; move K36l before pvzI26; pose proof (proj2 pvzI26) as K36r; move K36r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K71l; move K71l before pvzI27; pose proof (proj2 pvzI27) as K71r; move K71r before pvzI27; clear pvzI27.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E PbboCTr.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbboCTr.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbboCTr.kn0).
  { unfold know_ok, PbboCTr.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K66]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K67]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | byte_tac ltac:(clear) | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV50l HV50r K71l K71r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K70]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K71l K71r) | exact (conj K71l K71r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbboCTr.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbboCTr.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbboCTr.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K36l K36r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbboCTr.ps0) with 0xbba38 in Hms. change (SR.ps_regs PbboCTr.ps0) with (map (fun i => (i, nth i PbboCTr.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbboCTr.ps0) with PbboCTr.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbboCTr.regs0 PbboCTr.regs_out0 72 KS_bboCTr KS_bboCTr_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboCTr.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbboCTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbboITr := BndP_Eb_013S9.LibSegEb_bboITr.
Definition KS_bboITr : list nat := Eval vm_compute in (BG.kept_list 72 PbboITr.regs0 PbboITr.regs_out0).
Lemma KS_bboITr_ok : BG.kept_ok 72 PbboITr.regs0 PbboITr.regs_out0 KS_bboITr = true. Proof. vm_compute. reflexivity. Qed.
Lemma bboITr_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 36%nat) + 368) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 368) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 192)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 192) + 192 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 192)) ->
  6930432 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6930432 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 192) + 192 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1204292 <= (V 47%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 37%nat) -> L5.u64_at RSEGS M (V 37%nat) 1277312 -> L5KA.zeros_at M 2147610552 1 ->
  L5KA.zeros_at M 2147610553 1 -> L5.u8_at RSEGS M ((V 36%nat) + 16) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbb7e0 M) (st fx' R' 0xbba38 M')
        /\ (forall x, In x KS_bboITr -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 69%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 1
        /\ L5.defined M' ((V 47%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G18 G19 G20 G22 G23 G25 G26 G27 K0 K1 K2 pvzI20 K4 K5 pvzI21 K7 K8 K9 K10 K11 K12 K13 pvzI22 K15 K16 K17 K18 K19 pvzI23 K21 K22 K23 K24 K25 K26 K27 K28 pvzI24 K30 K31 K32 K33 K34 K35 pvzI25 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV58l; move HV58l before pvzI8; pose proof (proj2 pvzI8) as HV58r; move HV58r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV59l; move HV59l before pvzI9; pose proof (proj2 pvzI9) as HV59r; move HV59r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV60l; move HV60l before pvzI10; pose proof (proj2 pvzI10) as HV60r; move HV60r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV61l; move HV61l before pvzI11; pose proof (proj2 pvzI11) as HV61r; move HV61r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV62l; move HV62l before pvzI12; pose proof (proj2 pvzI12) as HV62r; move HV62r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV63l; move HV63l before pvzI13; pose proof (proj2 pvzI13) as HV63r; move HV63r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV64l; move HV64l before pvzI14; pose proof (proj2 pvzI14) as HV64r; move HV64r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV65l; move HV65l before pvzI15; pose proof (proj2 pvzI15) as HV65r; move HV65r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV66l; move HV66l before pvzI16; pose proof (proj2 pvzI16) as HV66r; move HV66r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV67l; move HV67l before pvzI17; pose proof (proj2 pvzI17) as HV67r; move HV67r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV68l; move HV68l before pvzI18; pose proof (proj2 pvzI18) as HV68r; move HV68r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV69l; move HV69l before pvzI19; pose proof (proj2 pvzI19) as HV69r; move HV69r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K6l; move K6l before pvzI21; pose proof (proj2 pvzI21) as K6r; move K6r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K14l; move K14l before pvzI22; pose proof (proj2 pvzI22) as K14r; move K14r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K20l; move K20l before pvzI23; pose proof (proj2 pvzI23) as K20r; move K20r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K29l; move K29l before pvzI24; pose proof (proj2 pvzI24) as K29r; move K29r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K36l; move K36l before pvzI25; pose proof (proj2 pvzI25) as K36r; move K36r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E PbboITr.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbboITr.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbboITr.kn0).
  { unfold know_ok, PbboITr.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K66]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K67]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | byte_tac ltac:(clear) | exactA K69]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbboITr.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbboITr.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbboITr.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K36l K36r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbboITr.ps0) with 0xbba38 in Hms. change (SR.ps_regs PbboITr.ps0) with (map (fun i => (i, nth i PbboITr.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbboITr.ps0) with PbboITr.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbboITr.regs0 PbboITr.regs_out0 72 KS_bboITr KS_bboITr_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboITr.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbboITr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbboTTr := BndP_Eb_014S9.LibSegEb_bboTTr.
Definition KS_bboTTr : list nat := Eval vm_compute in (BG.kept_list 72 PbboTTr.regs0 PbboTTr.regs_out0).
Lemma KS_bboTTr_ok : BG.kept_ok 72 PbboTTr.regs0 PbboTTr.regs_out0 KS_bboTTr = true. Proof. vm_compute. reflexivity. Qed.
Lemma bboTTr_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 368) -> getr R (reg 24) = Z_to_bv 64 ((((V 36%nat) + 368) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 192)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 192) + 192 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 192)) ->
  6930432 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6930432 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 192) + 192 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1204292 <= (V 47%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 37%nat) -> L5.u64_at RSEGS M (V 37%nat) 1277312 -> L5KA.zeros_at M 2147610552 1 ->
  L5KA.zeros_at M 2147610553 1 -> L5.u8_at RSEGS M ((V 36%nat) + 16) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 50%nat) -> 0 <= (V 50%nat) <= 16777216 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbbab8 M) (st fx' R' 0xbba38 M')
        /\ (forall x, In x KS_bboTTr -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 69%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 1
        /\ L5.defined M' ((V 47%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 G2 G8 G9 G18 G19 G20 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI21 K4 K5 pvzI22 K7 K8 K9 K10 K11 K12 K13 pvzI23 K15 K16 K17 K18 K19 pvzI24 K21 K22 K23 K24 K25 K26 K27 K28 pvzI25 K30 K31 K32 K33 K34 K35 pvzI26 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70 pvzI27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV58l; move HV58l before pvzI9; pose proof (proj2 pvzI9) as HV58r; move HV58r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV59l; move HV59l before pvzI10; pose proof (proj2 pvzI10) as HV59r; move HV59r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV60l; move HV60l before pvzI11; pose proof (proj2 pvzI11) as HV60r; move HV60r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV61l; move HV61l before pvzI12; pose proof (proj2 pvzI12) as HV61r; move HV61r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV62l; move HV62l before pvzI13; pose proof (proj2 pvzI13) as HV62r; move HV62r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV63l; move HV63l before pvzI14; pose proof (proj2 pvzI14) as HV63r; move HV63r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV64l; move HV64l before pvzI15; pose proof (proj2 pvzI15) as HV64r; move HV64r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV65l; move HV65l before pvzI16; pose proof (proj2 pvzI16) as HV65r; move HV65r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV66l; move HV66l before pvzI17; pose proof (proj2 pvzI17) as HV66r; move HV66r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV67l; move HV67l before pvzI18; pose proof (proj2 pvzI18) as HV67r; move HV67r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV68l; move HV68l before pvzI19; pose proof (proj2 pvzI19) as HV68r; move HV68r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV69l; move HV69l before pvzI20; pose proof (proj2 pvzI20) as HV69r; move HV69r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K3l; move K3l before pvzI21; pose proof (proj2 pvzI21) as K3r; move K3r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K6l; move K6l before pvzI22; pose proof (proj2 pvzI22) as K6r; move K6r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K14l; move K14l before pvzI23; pose proof (proj2 pvzI23) as K14r; move K14r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K20l; move K20l before pvzI24; pose proof (proj2 pvzI24) as K20r; move K20r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K29l; move K29l before pvzI25; pose proof (proj2 pvzI25) as K29r; move K29r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K36l; move K36l before pvzI26; pose proof (proj2 pvzI26) as K36r; move K36r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K71l; move K71l before pvzI27; pose proof (proj2 pvzI27) as K71r; move K71r before pvzI27; clear pvzI27.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E PbboTTr.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbboTTr.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbboTTr.kn0).
  { unfold know_ok, PbboTTr.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K66]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K67]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | byte_tac ltac:(clear) | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV50l HV50r K71l K71r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K70]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K71l K71r) | exact (conj K71l K71r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbboTTr.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbboTTr.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbboTTr.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K36l K36r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbboTTr.ps0) with 0xbba38 in Hms. change (SR.ps_regs PbboTTr.ps0) with (map (fun i => (i, nth i PbboTTr.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbboTTr.ps0) with PbboTTr.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbboTTr.regs0 PbboTTr.regs_out0 72 KS_bboTTr KS_bboTTr_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboTTr.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbboTTr.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbboZ1 := BndP_Eb_014S9.LibSegEb_bboZ1.
Definition KS_bboZ1 : list nat := Eval vm_compute in (BG.kept_list 72 PbboZ1.regs0 PbboZ1.regs_out0).
Lemma KS_bboZ1_ok : BG.kept_ok 72 PbboZ1.regs0 PbboZ1.regs_out0 KS_bboZ1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bboZ1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 65024 -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 192)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 192) + 192 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 192)) ->
  6930432 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6930432 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 192) + 192 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1204292 <= (V 47%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 69%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbbb34 M) (st fx' R' 0xbba38 M')
        /\ (forall x, In x KS_bboZ1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 69%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.defined M' ((V 47%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G18 G19 G20 G21 G23 G25 G26 G27 K0 K1 K2 pvzI20 K4 K5 pvzI21 K7 K8 K9 K10 K11 K12 K13 pvzI22 K15 K16 K17 K18 K19 pvzI23 K21 K22 K23 K24 K25 K26 K27 K28 pvzI24 K30 K31 K32 K33 K34 K35 pvzI25 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV58l; move HV58l before pvzI8; pose proof (proj2 pvzI8) as HV58r; move HV58r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV59l; move HV59l before pvzI9; pose proof (proj2 pvzI9) as HV59r; move HV59r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV60l; move HV60l before pvzI10; pose proof (proj2 pvzI10) as HV60r; move HV60r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV61l; move HV61l before pvzI11; pose proof (proj2 pvzI11) as HV61r; move HV61r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV62l; move HV62l before pvzI12; pose proof (proj2 pvzI12) as HV62r; move HV62r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV63l; move HV63l before pvzI13; pose proof (proj2 pvzI13) as HV63r; move HV63r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV64l; move HV64l before pvzI14; pose proof (proj2 pvzI14) as HV64r; move HV64r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV65l; move HV65l before pvzI15; pose proof (proj2 pvzI15) as HV65r; move HV65r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV66l; move HV66l before pvzI16; pose proof (proj2 pvzI16) as HV66r; move HV66r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV67l; move HV67l before pvzI17; pose proof (proj2 pvzI17) as HV67r; move HV67r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV68l; move HV68l before pvzI18; pose proof (proj2 pvzI18) as HV68r; move HV68r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV69l; move HV69l before pvzI19; pose proof (proj2 pvzI19) as HV69r; move HV69r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K6l; move K6l before pvzI21; pose proof (proj2 pvzI21) as K6r; move K6r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K14l; move K14l before pvzI22; pose proof (proj2 pvzI22) as K14r; move K14r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K20l; move K20l before pvzI23; pose proof (proj2 pvzI23) as K20r; move K20r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K29l; move K29l before pvzI24; pose proof (proj2 pvzI24) as K29r; move K29r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K36l; move K36l before pvzI25; pose proof (proj2 pvzI25) as K36r; move K36r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E PbboZ1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbboZ1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbboZ1.kn0).
  { unfold know_ok, PbboZ1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K64]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbboZ1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbboZ1.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbboZ1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K36l K36r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbboZ1.ps0) with 0xbba38 in Hms. change (SR.ps_regs PbboZ1.ps0) with (map (fun i => (i, nth i PbboZ1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbboZ1.ps0) with PbboZ1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbboZ1.regs0 PbboZ1.regs_out0 72 KS_bboZ1 KS_bboZ1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ1.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbboZ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbboZ11 := BndP_Eb_015S9.LibSegEb_bboZ11.
Definition KS_bboZ11 : list nat := Eval vm_compute in (BG.kept_list 72 PbboZ11.regs0 PbboZ11.regs_out0).
Lemma KS_bboZ11_ok : BG.kept_ok 72 PbboZ11.regs0 PbboZ11.regs_out0 KS_bboZ11 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bboZ11_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 37%nat) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 192)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 192) + 192 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 192)) ->
  6930432 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6930432 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 192) + 192 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1204292 <= (V 47%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 69%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbbb08 M) (st fx' R' 0xbba38 M')
        /\ (forall x, In x KS_bboZ11 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 69%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.defined M' ((V 47%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G18 G19 G20 G21 G25 G26 G27 K0 K1 K2 pvzI20 K4 K5 pvzI21 K7 K8 K9 K10 K11 K12 K13 pvzI22 K15 K16 K17 K18 K19 pvzI23 K21 K22 K23 K24 K25 K26 K27 K28 pvzI24 K30 K31 K32 K33 K34 K35 pvzI25 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV58l; move HV58l before pvzI8; pose proof (proj2 pvzI8) as HV58r; move HV58r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV59l; move HV59l before pvzI9; pose proof (proj2 pvzI9) as HV59r; move HV59r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV60l; move HV60l before pvzI10; pose proof (proj2 pvzI10) as HV60r; move HV60r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV61l; move HV61l before pvzI11; pose proof (proj2 pvzI11) as HV61r; move HV61r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV62l; move HV62l before pvzI12; pose proof (proj2 pvzI12) as HV62r; move HV62r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV63l; move HV63l before pvzI13; pose proof (proj2 pvzI13) as HV63r; move HV63r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV64l; move HV64l before pvzI14; pose proof (proj2 pvzI14) as HV64r; move HV64r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV65l; move HV65l before pvzI15; pose proof (proj2 pvzI15) as HV65r; move HV65r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV66l; move HV66l before pvzI16; pose proof (proj2 pvzI16) as HV66r; move HV66r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV67l; move HV67l before pvzI17; pose proof (proj2 pvzI17) as HV67r; move HV67r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV68l; move HV68l before pvzI18; pose proof (proj2 pvzI18) as HV68r; move HV68r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV69l; move HV69l before pvzI19; pose proof (proj2 pvzI19) as HV69r; move HV69r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K6l; move K6l before pvzI21; pose proof (proj2 pvzI21) as K6r; move K6r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K14l; move K14l before pvzI22; pose proof (proj2 pvzI22) as K14r; move K14r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K20l; move K20l before pvzI23; pose proof (proj2 pvzI23) as K20r; move K20r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K29l; move K29l before pvzI24; pose proof (proj2 pvzI24) as K29r; move K29r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K36l; move K36l before pvzI25; pose proof (proj2 pvzI25) as K36r; move K36r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E PbboZ11.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbboZ11.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbboZ11.kn0).
  { unfold know_ok, PbboZ11.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K64]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbboZ11.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbboZ11.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbboZ11.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K36l K36r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbboZ11.ps0) with 0xbba38 in Hms. change (SR.ps_regs PbboZ11.ps0) with (map (fun i => (i, nth i PbboZ11.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbboZ11.ps0) with PbboZ11.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbboZ11.regs0 PbboZ11.regs_out0 72 KS_bboZ11 KS_bboZ11_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ11.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbboZ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbboZc := BndP_Eb_015S9.LibSegEb_bboZc.
Definition KS_bboZc : list nat := Eval vm_compute in (BG.kept_list 72 PbboZc.regs0 PbboZc.regs_out0).
Lemma KS_bboZc_ok : BG.kept_ok 72 PbboZc.regs0 PbboZc.regs_out0 KS_bboZc = true. Proof. vm_compute. reflexivity. Qed.
Lemma bboZc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 65024 -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 192)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 192) + 192 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 192)) ->
  6930432 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6930432 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 192) + 192 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1204292 <= (V 47%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 69%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbb6bc M) (st fx' R' 0xbba38 M')
        /\ (forall x, In x KS_bboZc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 69%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.defined M' ((V 47%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G18 G19 G20 G21 G23 G25 G26 G27 K0 K1 K2 pvzI20 K4 K5 pvzI21 K7 K8 K9 K10 K11 K12 K13 pvzI22 K15 K16 K17 K18 K19 pvzI23 K21 K22 K23 K24 K25 K26 K27 K28 pvzI24 K30 K31 K32 K33 K34 K35 pvzI25 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV58l; move HV58l before pvzI8; pose proof (proj2 pvzI8) as HV58r; move HV58r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV59l; move HV59l before pvzI9; pose proof (proj2 pvzI9) as HV59r; move HV59r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV60l; move HV60l before pvzI10; pose proof (proj2 pvzI10) as HV60r; move HV60r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV61l; move HV61l before pvzI11; pose proof (proj2 pvzI11) as HV61r; move HV61r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV62l; move HV62l before pvzI12; pose proof (proj2 pvzI12) as HV62r; move HV62r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV63l; move HV63l before pvzI13; pose proof (proj2 pvzI13) as HV63r; move HV63r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV64l; move HV64l before pvzI14; pose proof (proj2 pvzI14) as HV64r; move HV64r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV65l; move HV65l before pvzI15; pose proof (proj2 pvzI15) as HV65r; move HV65r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV66l; move HV66l before pvzI16; pose proof (proj2 pvzI16) as HV66r; move HV66r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV67l; move HV67l before pvzI17; pose proof (proj2 pvzI17) as HV67r; move HV67r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV68l; move HV68l before pvzI18; pose proof (proj2 pvzI18) as HV68r; move HV68r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV69l; move HV69l before pvzI19; pose proof (proj2 pvzI19) as HV69r; move HV69r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K6l; move K6l before pvzI21; pose proof (proj2 pvzI21) as K6r; move K6r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K14l; move K14l before pvzI22; pose proof (proj2 pvzI22) as K14r; move K14r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K20l; move K20l before pvzI23; pose proof (proj2 pvzI23) as K20r; move K20r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K29l; move K29l before pvzI24; pose proof (proj2 pvzI24) as K29r; move K29r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K36l; move K36l before pvzI25; pose proof (proj2 pvzI25) as K36r; move K36r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E PbboZc.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbboZc.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbboZc.kn0).
  { unfold know_ok, PbboZc.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K64]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbboZc.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbboZc.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbboZc.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K36l K36r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbboZc.ps0) with 0xbba38 in Hms. change (SR.ps_regs PbboZc.ps0) with (map (fun i => (i, nth i PbboZc.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbboZc.ps0) with PbboZc.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbboZc.regs0 PbboZc.regs_out0 72 KS_bboZc KS_bboZc_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZc.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbboZc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbboZt := BndP_Eb_015S9.LibSegEb_bboZt.
Definition KS_bboZt : list nat := Eval vm_compute in (BG.kept_list 72 PbboZt.regs0 PbboZt.regs_out0).
Lemma KS_bboZt_ok : BG.kept_ok 72 PbboZt.regs0 PbboZt.regs_out0 KS_bboZt = true. Proof. vm_compute. reflexivity. Qed.
Lemma bboZt_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 65024 -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 192)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 192) + 192 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 192)) ->
  6930432 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6930432 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 192) + 192 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1204292 <= (V 47%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 69%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbb74c M) (st fx' R' 0xbba38 M')
        /\ (forall x, In x KS_bboZt -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 69%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.defined M' ((V 47%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G18 G19 G20 G21 G22 G23 G25 G26 G27 K0 K1 K2 pvzI20 K4 K5 pvzI21 K7 K8 K9 K10 K11 K12 K13 pvzI22 K15 K16 K17 K18 K19 pvzI23 K21 K22 K23 K24 K25 K26 K27 K28 pvzI24 K30 K31 K32 K33 K34 K35 pvzI25 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV58l; move HV58l before pvzI8; pose proof (proj2 pvzI8) as HV58r; move HV58r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV59l; move HV59l before pvzI9; pose proof (proj2 pvzI9) as HV59r; move HV59r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV60l; move HV60l before pvzI10; pose proof (proj2 pvzI10) as HV60r; move HV60r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV61l; move HV61l before pvzI11; pose proof (proj2 pvzI11) as HV61r; move HV61r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV62l; move HV62l before pvzI12; pose proof (proj2 pvzI12) as HV62r; move HV62r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV63l; move HV63l before pvzI13; pose proof (proj2 pvzI13) as HV63r; move HV63r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV64l; move HV64l before pvzI14; pose proof (proj2 pvzI14) as HV64r; move HV64r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV65l; move HV65l before pvzI15; pose proof (proj2 pvzI15) as HV65r; move HV65r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV66l; move HV66l before pvzI16; pose proof (proj2 pvzI16) as HV66r; move HV66r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV67l; move HV67l before pvzI17; pose proof (proj2 pvzI17) as HV67r; move HV67r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV68l; move HV68l before pvzI18; pose proof (proj2 pvzI18) as HV68r; move HV68r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV69l; move HV69l before pvzI19; pose proof (proj2 pvzI19) as HV69r; move HV69r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K6l; move K6l before pvzI21; pose proof (proj2 pvzI21) as K6r; move K6r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K14l; move K14l before pvzI22; pose proof (proj2 pvzI22) as K14r; move K14r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K20l; move K20l before pvzI23; pose proof (proj2 pvzI23) as K20r; move K20r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K29l; move K29l before pvzI24; pose proof (proj2 pvzI24) as K29r; move K29r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K36l; move K36l before pvzI25; pose proof (proj2 pvzI25) as K36r; move K36r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E PbboZt.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbboZt.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbboZt.kn0).
  { unfold know_ok, PbboZt.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K64]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbboZt.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbboZt.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbboZt.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K36l K36r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbboZt.ps0) with 0xbba38 in Hms. change (SR.ps_regs PbboZt.ps0) with (map (fun i => (i, nth i PbboZt.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbboZt.ps0) with PbboZt.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbboZt.regs0 PbboZt.regs_out0 72 KS_bboZt KS_bboZt_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbboZt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbboZt13 := BndP_Eb_015S9.LibSegEb_bboZt13.
Definition KS_bboZt13 : list nat := Eval vm_compute in (BG.kept_list 72 PbboZt13.regs0 PbboZt13.regs_out0).
Lemma KS_bboZt13_ok : BG.kept_ok 72 PbboZt13.regs0 PbboZt13.regs_out0 KS_bboZt13 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bboZt13_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 65024 -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 192)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 192) + 192 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 192)) ->
  6930432 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6930432 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 192) + 192 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1204292 <= (V 47%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 69%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbb61c M) (st fx' R' 0xbba38 M')
        /\ (forall x, In x KS_bboZt13 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 69%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.defined M' ((V 47%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI20 K4 K5 pvzI21 K7 K8 K9 K10 K11 K12 K13 pvzI22 K15 K16 K17 K18 K19 pvzI23 K21 K22 K23 K24 K25 K26 K27 K28 pvzI24 K30 K31 K32 K33 K34 K35 pvzI25 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV58l; move HV58l before pvzI8; pose proof (proj2 pvzI8) as HV58r; move HV58r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV59l; move HV59l before pvzI9; pose proof (proj2 pvzI9) as HV59r; move HV59r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV60l; move HV60l before pvzI10; pose proof (proj2 pvzI10) as HV60r; move HV60r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV61l; move HV61l before pvzI11; pose proof (proj2 pvzI11) as HV61r; move HV61r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV62l; move HV62l before pvzI12; pose proof (proj2 pvzI12) as HV62r; move HV62r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV63l; move HV63l before pvzI13; pose proof (proj2 pvzI13) as HV63r; move HV63r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV64l; move HV64l before pvzI14; pose proof (proj2 pvzI14) as HV64r; move HV64r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV65l; move HV65l before pvzI15; pose proof (proj2 pvzI15) as HV65r; move HV65r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV66l; move HV66l before pvzI16; pose proof (proj2 pvzI16) as HV66r; move HV66r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV67l; move HV67l before pvzI17; pose proof (proj2 pvzI17) as HV67r; move HV67r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV68l; move HV68l before pvzI18; pose proof (proj2 pvzI18) as HV68r; move HV68r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV69l; move HV69l before pvzI19; pose proof (proj2 pvzI19) as HV69r; move HV69r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K6l; move K6l before pvzI21; pose proof (proj2 pvzI21) as K6r; move K6r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K14l; move K14l before pvzI22; pose proof (proj2 pvzI22) as K14r; move K14r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K20l; move K20l before pvzI23; pose proof (proj2 pvzI23) as K20r; move K20r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K29l; move K29l before pvzI24; pose proof (proj2 pvzI24) as K29r; move K29r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K36l; move K36l before pvzI25; pose proof (proj2 pvzI25) as K36r; move K36r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E PbboZt13.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbboZt13.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbboZt13.kn0).
  { unfold know_ok, PbboZt13.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K64]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbboZt13.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbboZt13.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbboZt13.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K36l K36r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbboZt13.ps0) with 0xbba38 in Hms. change (SR.ps_regs PbboZt13.ps0) with (map (fun i => (i, nth i PbboZt13.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbboZt13.ps0) with PbboZt13.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbboZt13.regs0 PbboZt13.regs_out0 72 KS_bboZt13 KS_bboZt13_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZt13.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbboZt13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbboZ2 := BndP_Eb_015S9.LibSegEb_bboZ2.
Definition KS_bboZ2 : list nat := Eval vm_compute in (BG.kept_list 72 PbboZ2.regs0 PbboZ2.regs_out0).
Lemma KS_bboZ2_ok : BG.kept_ok 72 PbboZ2.regs0 PbboZ2.regs_out0 KS_bboZ2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bboZ2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 65024 -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 6930432 <= (V 36%nat) <= 140737488354944 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 384 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 3 -> L5KA.zeros_at M ((((V 36%nat) + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M ((((V 36%nat) + 20) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 36%nat) 384 -> (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 384 <= ((V 2%nat) - 192)) -> 6930432 <= (V 38%nat) <= 140737488355312 -> aligned (V 38%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) 2 -> L5.writable RSEGS M (V 38%nat) 16 -> (((V 2%nat) - 192) + 192 <= (V 38%nat) \/ (V 38%nat) + 16 <= ((V 2%nat) - 192)) ->
  6930432 <= (V 37%nat) <= 140737488355320 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 37%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 8 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 38%nat) \/ (V 38%nat) + 16 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 36%nat)) ->
  ((V 38%nat) + 16 <= (V 37%nat) \/ (V 37%nat) + 8 <= (V 38%nat)) -> 6930432 <= (V 47%nat) <= 140737488355264 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 64 ->
  L5.writable RSEGS M (V 47%nat) 64 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 47%nat) + 56) (V 48%nat) ->
  4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 64 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) ->
  (((V 2%nat) - 192) + 192 <= (V 47%nat) \/ (V 47%nat) + 64 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 384 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 36%nat)) -> ((V 36%nat) + 384 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 48 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 38%nat) + 16 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 38%nat)) -> ((V 38%nat) + 16 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 38%nat)) -> ((((V 38%nat) / 8) + 2147450880) + 2 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 38%nat) / 8) + 2147450880)) ->
  ((V 37%nat) + 8 <= (V 47%nat) \/ (V 47%nat) + 64 <= (V 37%nat)) -> ((V 37%nat) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 37%nat)) -> ((((V 37%nat) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 8 <= (((V 37%nat) / 8) + 2147450880)) -> ((V 47%nat) + 64 <= 65536 \/ 65536 + 1204292 <= (V 47%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 69%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 8) <= bv_unsigned a < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 8) <= i < ((V 36%nat) + 8) + 1) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbbb60 M) (st fx' R' 0xbba38 M')
        /\ (forall x, In x KS_bboZ2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 69%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.defined M' ((V 47%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G18 G19 G20 G21 G23 G25 G26 G27 K0 K1 K2 pvzI20 K4 K5 pvzI21 K7 K8 K9 K10 K11 K12 K13 pvzI22 K15 K16 K17 K18 K19 pvzI23 K21 K22 K23 K24 K25 K26 K27 K28 pvzI24 K30 K31 K32 K33 K34 K35 pvzI25 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV57l; move HV57l before pvzI7; pose proof (proj2 pvzI7) as HV57r; move HV57r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV58l; move HV58l before pvzI8; pose proof (proj2 pvzI8) as HV58r; move HV58r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV59l; move HV59l before pvzI9; pose proof (proj2 pvzI9) as HV59r; move HV59r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV60l; move HV60l before pvzI10; pose proof (proj2 pvzI10) as HV60r; move HV60r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV61l; move HV61l before pvzI11; pose proof (proj2 pvzI11) as HV61r; move HV61r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV62l; move HV62l before pvzI12; pose proof (proj2 pvzI12) as HV62r; move HV62r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV63l; move HV63l before pvzI13; pose proof (proj2 pvzI13) as HV63r; move HV63r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV64l; move HV64l before pvzI14; pose proof (proj2 pvzI14) as HV64r; move HV64r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV65l; move HV65l before pvzI15; pose proof (proj2 pvzI15) as HV65r; move HV65r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV66l; move HV66l before pvzI16; pose proof (proj2 pvzI16) as HV66r; move HV66r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV67l; move HV67l before pvzI17; pose proof (proj2 pvzI17) as HV67r; move HV67r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV68l; move HV68l before pvzI18; pose proof (proj2 pvzI18) as HV68r; move HV68r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV69l; move HV69l before pvzI19; pose proof (proj2 pvzI19) as HV69r; move HV69r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K6l; move K6l before pvzI21; pose proof (proj2 pvzI21) as K6r; move K6r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K14l; move K14l before pvzI22; pose proof (proj2 pvzI22) as K14r; move K14r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K20l; move K20l before pvzI23; pose proof (proj2 pvzI23) as K20r; move K20r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K29l; move K29l before pvzI24; pose proof (proj2 pvzI24) as K29r; move K29r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K36l; move K36l before pvzI25; pose proof (proj2 pvzI25) as K36r; move K36r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E PbboZ2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbboZ2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbboZ2.kn0).
  { unfold know_ok, PbboZ2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | clear - HV47l HV47r K29l K29r; lia | clear - HV47l HV47r K29l K29r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | clear - HV48l HV48r K36l K36r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K36l K36r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K29l K29r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K64]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbboZ2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbboZ2.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 8) <= bv_unsigned a < (vz_36 + 8) + 1) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbboZ2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K36l K36r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbboZ2.ps0) with 0xbba38 in Hms. change (SR.ps_regs PbboZ2.ps0) with (map (fun i => (i, nth i PbboZ2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbboZ2.ps0) with PbboZ2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbboZ2.regs0 PbboZ2.regs_out0 72 KS_bboZ2 KS_bboZ2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbboZ2.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbboZ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

End PEBBOP3.
