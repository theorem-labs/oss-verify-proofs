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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_054S9 BndP_Eb_055S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMBSRP3.
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

Module PbsrXge := BndP_Eb_054S9.LibSegEb_bsrXge.
Definition KS_bsrXge : list nat := Eval vm_compute in (BG.kept_list 80 PbsrXge.regs0 PbsrXge.regs_out0).
Lemma KS_bsrXge_ok : BG.kept_ok 80 PbsrXge.regs0 PbsrXge.regs_out0 KS_bsrXge = true. Proof. vm_compute. reflexivity. Qed.
Lemma bsrXge_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 50%nat) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 (V 50%nat) -> getr R (reg 10) = Z_to_bv 64 16384 -> getr R (reg 18) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 22) = Z_to_bv 64 ((V 36%nat) + 240) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 24) = Z_to_bv 64 ((((V 36%nat) + 240) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487168 <= (V 50%nat) <= 140737488355168 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 56 -> L5.u64_at RSEGS M ((V 50%nat) + 24) (V 37%nat) -> 4096 <= (V 37%nat) <= 140737488338944 ->
  L5.u64_at RSEGS M ((V 50%nat) + 8) ((V 47%nat) + 32) -> L5.u64_at RSEGS M ((V 50%nat) + 16) (V 47%nat) -> L5.u64_at RSEGS M ((V 50%nat) + 48) (V 47%nat) -> 6930432 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  ((V 50%nat) + 56 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 50%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.defined M ((V 36%nat) + 256) 8 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> 6930432 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> ((V 36%nat) + 296 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 36%nat)) -> ((V 36%nat) + 296 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 37 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 36%nat) / 8) + 2147450880)) ->
  ((V 50%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 50%nat)) -> ((V 50%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 50%nat)) -> ((V 47%nat) + 128 <= 65536 \/ 65536 + 1200196 <= (V 47%nat)) -> L5.u64_at RSEGS M ((V 47%nat) + 32) 16384 ->
  6930432 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 -> (2147446784 + 17592186048512 <= (V 45%nat) \/ (V 45%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 45%nat) / 8) + 2147450880) 34 ->
  L5.writable RSEGS M (V 45%nat) 272 -> ((V 36%nat) + 296 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) -> ((V 50%nat) + 56 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 50%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 45%nat) + 16) -> L5.u64_at RSEGS M (V 45%nat) 1291576 -> L5.u64_at RSEGS M ((V 45%nat) + 16) 1291336 -> L5.u32_at RSEGS M ((V 45%nat) + 152) 0 ->
  L5.u32_at RSEGS M ((V 45%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 160) ((V 45%nat) + 16) -> L5KA.zeros_at M 2147612324 1 -> L5KA.zeros_at M 2147612305 1 ->
  ((V 45%nat) + 272 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 45%nat)) -> ((V 45%nat) + 272 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 45%nat)) -> ((((V 47%nat) / 8) + 2147450880) + 16 <= (((V 45%nat) / 8) + 2147450880) \/ (((V 45%nat) / 8) + 2147450880) + 34 <= (((V 47%nat) / 8) + 2147450880)) -> ((((V 47%nat) / 8) + 2147450880) + 16 <= 2147612324 \/ 2147612324 + 1 <= (((V 47%nat) / 8) + 2147450880)) ->
  ((((V 47%nat) / 8) + 2147450880) + 16 <= 2147612305 \/ 2147612305 + 1 <= (((V 47%nat) / 8) + 2147450880)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9568 M) (st fx' R' 0xb9628 M')
        /\ (forall x, In x KS_bsrXge -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 256)
        /\ getr R' (reg 18) = Z_to_bv 64 16384
        /\ getr R' (reg 22) = Z_to_bv 64 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G18 G19 G20 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI10 K4 K5 K6 pvzI11 K8 K9 K10 pvzI12 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 pvzI13 K23 K24 K25 K26 K27 K28 pvzI14 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 pvzI15 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV47l; move HV47l before pvzI7; pose proof (proj2 pvzI7) as HV47r; move HV47r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K7l; move K7l before pvzI11; pose proof (proj2 pvzI11) as K7r; move K7r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K11l; move K11l before pvzI12; pose proof (proj2 pvzI12) as K11r; move K11r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K22l; move K22l before pvzI13; pose proof (proj2 pvzI13) as K22r; move K22r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K29l; move K29l before pvzI14; pose proof (proj2 pvzI14) as K29r; move K29r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K40l; move K40l before pvzI15; pose proof (proj2 pvzI15) as K40r; move K40r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 45%nat => Z_to_bv 64 vz_45 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 45%nat => vz_45 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbsrXge.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbsrXge.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbsrXge.kn0).
  { unfold know_ok, PbsrXge.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57; lia | clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57; lia | clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | clear; lia | exact K41]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | exactA K53]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K54]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | generalize K56; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | evalEk ZA ltac:(clear) | generalize K57; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | generalize K58; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K59; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K60; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbsrXge.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbsrXge.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbsrXge.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbsrXge.ps0) with 0xb9628 in Hms. change (SR.ps_regs PbsrXge.ps0) with (map (fun i => (i, nth i PbsrXge.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbsrXge.ps0) with PbsrXge.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbsrXge.regs0 PbsrXge.regs_out0 80 KS_bsrXge KS_bsrXge_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbsrXge.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbsrXge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrXge.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbsrXge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrXge.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbsrXge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbsrXlt := BndP_Eb_055S9.LibSegEb_bsrXlt.
Definition KS_bsrXlt : list nat := Eval vm_compute in (BG.kept_list 80 PbsrXlt.regs0 PbsrXlt.regs_out0).
Lemma KS_bsrXlt_ok : BG.kept_ok 80 PbsrXlt.regs0 PbsrXlt.regs_out0 KS_bsrXlt = true. Proof. vm_compute. reflexivity. Qed.
Lemma bsrXlt_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 50%nat) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 (V 50%nat) -> getr R (reg 10) = Z_to_bv 64 (V 51%nat) -> getr R (reg 18) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 0 -> getr R (reg 22) = Z_to_bv 64 ((V 36%nat) + 240) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 24) = Z_to_bv 64 ((((V 36%nat) + 240) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487168 <= (V 50%nat) <= 140737488355168 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 56 -> L5.u64_at RSEGS M ((V 50%nat) + 24) (V 37%nat) -> 4096 <= (V 37%nat) <= 140737488338944 ->
  L5.u64_at RSEGS M ((V 50%nat) + 8) ((V 47%nat) + 32) -> L5.u64_at RSEGS M ((V 50%nat) + 16) (V 47%nat) -> L5.u64_at RSEGS M ((V 50%nat) + 48) (V 47%nat) -> 6930432 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  ((V 50%nat) + 56 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 50%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.defined M ((V 36%nat) + 256) 8 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> 6930432 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> ((V 36%nat) + 296 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 36%nat)) -> ((V 36%nat) + 296 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 37 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 36%nat) / 8) + 2147450880)) ->
  ((V 50%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 50%nat)) -> ((V 50%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 50%nat)) -> ((V 47%nat) + 128 <= 65536 \/ 65536 + 1200196 <= (V 47%nat)) -> L5.u64_at RSEGS M ((V 47%nat) + 32) 16384 ->
  6930432 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 -> (2147446784 + 17592186048512 <= (V 45%nat) \/ (V 45%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 45%nat) / 8) + 2147450880) 34 ->
  L5.writable RSEGS M (V 45%nat) 272 -> ((V 36%nat) + 296 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) -> ((V 50%nat) + 56 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 50%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 45%nat) + 16) -> L5.u64_at RSEGS M (V 45%nat) 1291576 -> L5.u64_at RSEGS M ((V 45%nat) + 16) 1291336 -> L5.u32_at RSEGS M ((V 45%nat) + 152) 0 ->
  L5.u32_at RSEGS M ((V 45%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 160) ((V 45%nat) + 16) -> L5KA.zeros_at M 2147612324 1 -> L5KA.zeros_at M 2147612305 1 ->
  ((V 45%nat) + 272 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 45%nat)) -> ((V 45%nat) + 272 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 45%nat)) -> ((((V 47%nat) / 8) + 2147450880) + 16 <= (((V 45%nat) / 8) + 2147450880) \/ (((V 45%nat) / 8) + 2147450880) + 34 <= (((V 47%nat) / 8) + 2147450880)) -> ((((V 47%nat) / 8) + 2147450880) + 16 <= 2147612324 \/ 2147612324 + 1 <= (((V 47%nat) / 8) + 2147450880)) ->
  ((((V 47%nat) / 8) + 2147450880) + 16 <= 2147612305 \/ 2147612305 + 1 <= (((V 47%nat) / 8) + 2147450880)) -> 0 <= (V 51%nat) <= 16383 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> ~ (((V 45%nat) + 152) <= bv_unsigned a < ((V 45%nat) + 152) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> ~ (((V 45%nat) + 152) <= i < ((V 45%nat) + 152) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9568 M) (st fx' R' 0xb9628 M')
        /\ (forall x, In x KS_bsrXlt -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 759272
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 256)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ L5.u32_at RSEGS M' ((V 45%nat) + 152) 2
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G18 G19 G20 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI11 K4 K5 K6 pvzI12 K8 K9 K10 pvzI13 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 pvzI14 K23 K24 K25 K26 K27 K28 pvzI15 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 pvzI16 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV47l; move HV47l before pvzI7; pose proof (proj2 pvzI7) as HV47r; move HV47r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K11l; move K11l before pvzI13; pose proof (proj2 pvzI13) as K11r; move K11r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K22l; move K22l before pvzI14; pose proof (proj2 pvzI14) as K22r; move K22r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K29l; move K29l before pvzI15; pose proof (proj2 pvzI15) as K29r; move K29r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K40l; move K40l before pvzI16; pose proof (proj2 pvzI16) as K40r; move K40r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K61l; move K61l before pvzI17; pose proof (proj2 pvzI17) as K61r; move K61r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 45%nat => Z_to_bv 64 vz_45 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 45%nat => vz_45 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PbsrXlt.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbsrXlt.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbsrXlt.kn0).
  { unfold know_ok, PbsrXlt.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | clear - HV50l HV50r K3l K3r K16 K36 K37 K46; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57; lia | clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57; lia | clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | clear; lia | exact K41]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37 K46) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58; lia | exactA K53]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K54]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | generalize K56; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37 K57) | evalEk ZA ltac:(clear) | generalize K57; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk ZA ltac:(clear) | generalize K58; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K59; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38 K56 K58 K59 K60) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K60; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K61l K61r) | exact (conj K61l K61r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbsrXlt.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbsrXlt.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> ~ ((vz_45 + 152) <= bv_unsigned a < (vz_45 + 152) + 4) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PbsrXlt.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk' ZA Hag ltac:(clear) | clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbsrXlt.ps0) with 0xb9628 in Hms. change (SR.ps_regs PbsrXlt.ps0) with (map (fun i => (i, nth i PbsrXlt.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbsrXlt.ps0) with PbsrXlt.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbsrXlt.regs0 PbsrXlt.regs_out0 80 KS_bsrXlt KS_bsrXlt_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbsrXlt.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbsrXlt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrXlt.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbsrXlt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrXlt.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbsrXlt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrXlt.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbsrXlt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrXlt.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbsrXlt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrXlt.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbsrXlt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV45l HV45r K40l K40r K42 K45 K46 K56 K57 K58) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 K45) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbsrR := BndP_Eb_054S9.LibSegEb_bsrR.
Definition KS_bsrR : list nat := Eval vm_compute in (BG.kept_list 80 PbsrR.regs0 PbsrR.regs_out0).
Lemma KS_bsrR_ok : BG.kept_ok 80 PbsrR.regs0 PbsrR.regs_out0 KS_bsrR = true. Proof. vm_compute. reflexivity. Qed.
Lemma bsrR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 50%nat) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 (V 50%nat) -> getr R (reg 22) = Z_to_bv 64 (V 41%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 140735332487168 <= (V 50%nat) <= 140737488355168 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 56 -> L5.u64_at RSEGS M ((V 50%nat) + 16) (V 47%nat) -> 6930432 <= (V 47%nat) <= 140737488355200 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> ((V 36%nat) + 296 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 36%nat)) -> ((V 36%nat) + 296 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) ->
  ((((V 36%nat) / 8) + 2147450880) + 37 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 50%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 50%nat)) -> ((V 50%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 50%nat)) -> ((V 47%nat) + 128 <= 65536 \/ 65536 + 1200196 <= (V 47%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 76%nat) -> (((V 2%nat) - 104) + 104 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 104)) -> (((V 2%nat) - 104) + 104 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 104)) -> (((V 2%nat) - 104) + 104 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((V 2%nat) - 104)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9628 M) (st fx' R' 0xb96fc M')
        /\ (forall x, In x KS_bsrR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 76%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450895) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450894) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450893) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450892) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.defined M' ((V 47%nat) + 8) 120).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G22 G25 G26 pvzI20 K1 K2 pvzI21 K4 K5 K6 pvzI22 K8 K9 K10 K11 K12 K13 pvzI23 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV41l; move HV41l before pvzI3; pose proof (proj2 pvzI3) as HV41r; move HV41r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV64l; move HV64l before pvzI7; pose proof (proj2 pvzI7) as HV64r; move HV64r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV65l; move HV65l before pvzI8; pose proof (proj2 pvzI8) as HV65r; move HV65r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV66l; move HV66l before pvzI9; pose proof (proj2 pvzI9) as HV66r; move HV66r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV67l; move HV67l before pvzI10; pose proof (proj2 pvzI10) as HV67r; move HV67r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV68l; move HV68l before pvzI11; pose proof (proj2 pvzI11) as HV68r; move HV68r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV69l; move HV69l before pvzI12; pose proof (proj2 pvzI12) as HV69r; move HV69r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV70l; move HV70l before pvzI13; pose proof (proj2 pvzI13) as HV70r; move HV70r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV71l; move HV71l before pvzI14; pose proof (proj2 pvzI14) as HV71r; move HV71r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV72l; move HV72l before pvzI15; pose proof (proj2 pvzI15) as HV72r; move HV72r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV73l; move HV73l before pvzI16; pose proof (proj2 pvzI16) as HV73r; move HV73r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV74l; move HV74l before pvzI17; pose proof (proj2 pvzI17) as HV74r; move HV74r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV75l; move HV75l before pvzI18; pose proof (proj2 pvzI18) as HV75r; move HV75r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV76l; move HV76l before pvzI19; pose proof (proj2 pvzI19) as HV76r; move HV76r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K0l; move K0l before pvzI20; pose proof (proj2 pvzI20) as K0r; move K0r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K3l; move K3l before pvzI21; pose proof (proj2 pvzI21) as K3r; move K3r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K7l; move K7l before pvzI22; pose proof (proj2 pvzI22) as K7r; move K7r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K14l; move K14l before pvzI23; pose proof (proj2 pvzI23) as K14r; move K14r before pvzI23; clear pvzI23.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *. set (vz_76 := V 76%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 41%nat => Z_to_bv 64 vz_41 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | 76%nat => Z_to_bv 64 vz_76 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 41%nat => vz_41 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | 76%nat => vz_76 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 77%nat. }
  assert (HR: regs_ok E PbsrR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbsrR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbsrR.kn0).
  { unfold know_ok, PbsrR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K21 K22) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K21 K22) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K21 K22) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K21 K22; lia | clear - HV50l HV50r K3l K3r K21 K22; lia | clear - HV50l HV50r K3l K3r K21 K22; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K21 K22) | evalEk ZA ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | clear - HV50l HV50r K3l K3r K21 K22; lia | clear - HV50l HV50r K3l K3r K21 K22; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39; lia | clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39; lia | clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39; lia | clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39; lia | clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39; lia | clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39; lia | clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K22 K38) | clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39; lia | clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K22 K38) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K22 K38) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19 K22 K38; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K22 K38; lia | clear - HV48l HV48r K14l K14r K16 K17 K19 K22 K38; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K22 K38) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K22 K38) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K18 K19 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K18 K19 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K22 K38) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K18 K19 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K21 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K21 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K22 K38) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear - HV76l HV76r) | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | clear - HV2l HV2r K0l K0r K37 K38 K39; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K22 K38) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K37 K38 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbsrR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbsrR.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbsrR.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K22 K38) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K14l K14r K16 K17 K19 K22 K38 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbsrR.ps0) with 0xb96fc in Hms. change (SR.ps_regs PbsrR.ps0) with (map (fun i => (i, nth i PbsrR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbsrR.ps0) with PbsrR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbsrR.regs0 PbsrR.regs_out0 80 KS_bsrR KS_bsrR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrR.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbsrR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K14l K14r K16 K17 K19 K22 K38) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 18); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K7l K7r K11 K17 K18 K20 K21 K23 K37 K39) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

End PMBSRP3.
