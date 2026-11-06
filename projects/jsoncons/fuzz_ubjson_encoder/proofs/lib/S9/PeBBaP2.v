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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_010S9 BndP_Eb_011S9 BndP_Eb_012S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBBAP2.
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

Module PbbaC1 := BndP_Eb_010S9.LibSegEb_bbaC1.
Definition KS_bbaC1 : list nat := Eval vm_compute in (BG.kept_list 72 PbbaC1.regs0 PbbaC1.regs_out0).
Lemma KS_bbaC1_ok : BG.kept_ok 72 PbbaC1.regs0 PbbaC1.regs_out0 KS_bbaC1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaC1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
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
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbade8 M) (st fx' R' 0xba0f8 M')
        /\ (forall x, In x KS_bbaC1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 765428
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 38%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G19 G20 G21 G23 G25 G26 G27 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 pvzI9 K15 K16 K17 K18 K19 pvzI10 K21 K22 K23 K24 K25 K26 K27 K28 pvzI11 K30 K31 K32 K33 K34 K35 pvzI12 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K20l; move K20l before pvzI10; pose proof (proj2 pvzI10) as K20r; move K20r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K29l; move K29l before pvzI11; pose proof (proj2 pvzI11) as K29r; move K29r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K36l; move K36l before pvzI12; pose proof (proj2 pvzI12) as K36r; move K36r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbbaC1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaC1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaC1.kn0).
  { unfold know_ok, PbbaC1.kn0.
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
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaC1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaC1.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PbbaC1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaC1.ps0) with 0xba0f8 in Hms. change (SR.ps_regs PbbaC1.ps0) with (map (fun i => (i, nth i PbbaC1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaC1.ps0) with PbbaC1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaC1.regs0 PbbaC1.regs_out0 72 KS_bbaC1 KS_bbaC1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaC1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaC1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaC1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PbbaC1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaC1.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.

Module PbbaCe := BndP_Eb_010S9.LibSegEb_bbaCe.
Definition KS_bbaCe : list nat := Eval vm_compute in (BG.kept_list 72 PbbaCe.regs0 PbbaCe.regs_out0).
Lemma KS_bbaCe_ok : BG.kept_ok 72 PbbaCe.regs0 PbbaCe.regs_out0 KS_bbaCe = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaCe_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 65024 -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 69%nat) -> L5.u32_at RSEGS M (V 38%nat) (V 49%nat) -> 1 <= (V 49%nat) <= 64 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbadf4 M) (st fx' R' 0xbb150 M')
        /\ (forall x, In x KS_bbaCe -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 49%nat)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat)
        /\ L5.defined M' ((V 47%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 G2 G8 G9 G10 G18 G19 G20 G21 G23 G25 G26 G27 K0 K1 K2 pvzI22 K4 K5 pvzI23 K7 K8 K9 K10 K11 K12 K13 pvzI24 K15 K16 K17 K18 K19 pvzI25 K21 K22 K23 K24 K25 K26 K27 K28 pvzI26 K30 K31 K32 K33 K34 K35 pvzI27 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 pvzI28.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV49l; move HV49l before pvzI7; pose proof (proj2 pvzI7) as HV49r; move HV49r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV57l; move HV57l before pvzI9; pose proof (proj2 pvzI9) as HV57r; move HV57r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV58l; move HV58l before pvzI10; pose proof (proj2 pvzI10) as HV58r; move HV58r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV59l; move HV59l before pvzI11; pose proof (proj2 pvzI11) as HV59r; move HV59r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV60l; move HV60l before pvzI12; pose proof (proj2 pvzI12) as HV60r; move HV60r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV61l; move HV61l before pvzI13; pose proof (proj2 pvzI13) as HV61r; move HV61r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV62l; move HV62l before pvzI14; pose proof (proj2 pvzI14) as HV62r; move HV62r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV63l; move HV63l before pvzI15; pose proof (proj2 pvzI15) as HV63r; move HV63r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV64l; move HV64l before pvzI16; pose proof (proj2 pvzI16) as HV64r; move HV64r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV65l; move HV65l before pvzI17; pose proof (proj2 pvzI17) as HV65r; move HV65r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV66l; move HV66l before pvzI18; pose proof (proj2 pvzI18) as HV66r; move HV66r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV67l; move HV67l before pvzI19; pose proof (proj2 pvzI19) as HV67r; move HV67r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV68l; move HV68l before pvzI20; pose proof (proj2 pvzI20) as HV68r; move HV68r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV69l; move HV69l before pvzI21; pose proof (proj2 pvzI21) as HV69r; move HV69r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K3l; move K3l before pvzI22; pose proof (proj2 pvzI22) as K3r; move K3r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K6l; move K6l before pvzI23; pose proof (proj2 pvzI23) as K6r; move K6r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K14l; move K14l before pvzI24; pose proof (proj2 pvzI24) as K14r; move K14r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K20l; move K20l before pvzI25; pose proof (proj2 pvzI25) as K20r; move K20r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K29l; move K29l before pvzI26; pose proof (proj2 pvzI26) as K29r; move K29r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K36l; move K36l before pvzI27; pose proof (proj2 pvzI27) as K36r; move K36r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K66l; move K66l before pvzI28; pose proof (proj2 pvzI28) as K66r; move K66r before pvzI28; clear pvzI28.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E PbbaCe.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaCe.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaCe.kn0).
  { unfold know_ok, PbbaCe.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear - HV49l HV49r K66l K66r) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K66l K66r) | exact (conj K66l K66r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaCe.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaCe.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbbaCe.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K36l K36r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaCe.ps0) with 0xbb150 in Hms. change (SR.ps_regs PbbaCe.ps0) with (map (fun i => (i, nth i PbbaCe.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaCe.ps0) with PbbaCe.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaCe.regs0 PbbaCe.regs_out0 72 KS_bbaCe KS_bbaCe_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCe.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbbaCe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbbaCf := BndP_Eb_010S9.LibSegEb_bbaCf.
Definition KS_bbaCf_0 : list nat := Eval vm_compute in (BG.kept_list 72 PbbaCf.regs0 PbbaCf.regs_out0).
Lemma KS_bbaCf_0_ok : BG.kept_ok 72 PbbaCf.regs0 PbbaCf.regs_out0 KS_bbaCf_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bbaCf_1 : list nat := Eval vm_compute in (BG.kept_list 72 PbbaCf.regs0 PbbaCf.regs_out1).
Lemma KS_bbaCf_1_ok : BG.kept_ok 72 PbbaCf.regs0 PbbaCf.regs_out1 KS_bbaCf_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaCf_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 65024 -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
  L5.u64_at RSEGS M ((V 36%nat) + 368) (V 53%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 376) (V 54%nat) -> 0 <= (V 53%nat) <= 140737488355328 -> 0 <= (V 54%nat) <= 140737488355328 ->
  L5.u32_at RSEGS M (V 38%nat) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 328) 16777216 -> 0 <= (V 50%nat) <= 16777216 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 116) <= bv_unsigned a < ((V 2%nat) - 116) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 116) <= i < ((V 2%nat) - 116) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xbadf4 M) (st fx' R' 0xbc4d0 M')
        /\ (forall x, In x KS_bbaCf_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 765876
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 360)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 116)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 36%nat) + 368)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 36%nat) + 368) / 8) + 2147450880)
        /\ (V 53%nat) < (V 54%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 116) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat))
      \/ (msteps RSEGS (st fx R 0xbadf4 M) (st fx' R' 0xbc64c M')
        /\ (forall x, In x KS_bbaCf_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 765960
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 360)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 116)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 36%nat) + 368)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 36%nat) + 368) / 8) + 2147450880)
        /\ (V 54%nat) <= (V 53%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 116) 2
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G18 G19 G20 G21 G23 G25 G26 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 K13 pvzI12 K15 K16 K17 K18 K19 pvzI13 K21 K22 K23 K24 K25 K26 K27 K28 pvzI14 K30 K31 K32 K33 K34 K35 pvzI15 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 pvzI16 pvzI17 K56 K57 pvzI18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV53l; move HV53l before pvzI8; pose proof (proj2 pvzI8) as HV53r; move HV53r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV54l; move HV54l before pvzI9; pose proof (proj2 pvzI9) as HV54r; move HV54r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K20l; move K20l before pvzI13; pose proof (proj2 pvzI13) as K20r; move K20r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K29l; move K29l before pvzI14; pose proof (proj2 pvzI14) as K29r; move K29r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K36l; move K36l before pvzI15; pose proof (proj2 pvzI15) as K36r; move K36r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K54l; move K54l before pvzI16; pose proof (proj2 pvzI16) as K54r; move K54r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K55l; move K55l before pvzI17; pose proof (proj2 pvzI17) as K55r; move K55r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K58l; move K58l before pvzI18; pose proof (proj2 pvzI18) as K58r; move K58r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | 53%nat => vz_53 | 54%nat => vz_54 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PbbaCf.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaCf.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaCf.kn0).
  { unfold know_ok, PbbaCf.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear - HV53l HV53r K54l K54r) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear - HV54l HV54r K55l K55r) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K54l K54r) | exact (conj K54l K54r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV54l HV54r K55l K55r) | exact (conj K55l K55r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K58l K58r) | exact (conj K58l K58r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaCf.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaCf.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 116) <= bv_unsigned a < (vz_2 - 116) + 12) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaCf.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PbbaCf.ps0) with 0xbc4d0 in Hms. change (SR.ps_regs PbbaCf.ps0) with (map (fun i => (i, nth i PbbaCf.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbbaCf.ps0) with PbbaCf.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaCf.regs0 PbbaCf.regs_out0 72 KS_bbaCf_0 KS_bbaCf_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbbaCf.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaCf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaCf.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaCf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaCf.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaCf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaCf.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaCf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaCf.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbbaCf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaCf.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbbaCf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaCf.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbbaCf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K58l K58r) | clear; lia].
  - right.
    change (SR.ps_pc PbbaCf.ps1) with 0xbc64c in Hms. change (SR.ps_regs PbbaCf.ps1) with (map (fun i => (i, nth i PbbaCf.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbbaCf.ps1) with PbbaCf.cells1 in Hcells. unfold PbbaCf.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaCf.regs0 PbbaCf.regs_out1 72 KS_bbaCf_1 KS_bbaCf_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbbaCf.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaCf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaCf.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaCf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaCf.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaCf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaCf.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaCf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaCf.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PbbaCf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaCf.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth PbbaCf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaCf.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PbbaCf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K58l K58r) | clear; lia].
Qed.

Module PbbaCx := BndP_Eb_010S9.LibSegEb_bbaCx.
Definition KS_bbaCx : list nat := Eval vm_compute in (BG.kept_list 72 PbbaCx.regs0 PbbaCx.regs_out0).
Lemma KS_bbaCx_ok : BG.kept_ok 72 PbbaCx.regs0 PbbaCx.regs_out0 KS_bbaCx = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaCx_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 65024 -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
  L5.u32_at RSEGS M (V 38%nat) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 328) 16777216 -> 16777217 <= (V 50%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbadf4 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_bbaCx -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 765496
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 13
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 G19 G20 G21 G23 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 pvzI11 K21 K22 K23 K24 K25 K26 K27 K28 pvzI12 K30 K31 K32 K33 K34 K35 pvzI13 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K20l; move K20l before pvzI11; pose proof (proj2 pvzI11) as K20r; move K20r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K29l; move K29l before pvzI12; pose proof (proj2 pvzI12) as K29r; move K29r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K36l; move K36l before pvzI13; pose proof (proj2 pvzI13) as K36r; move K36r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K54l; move K54l before pvzI14; pose proof (proj2 pvzI14) as K54r; move K54r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbbaCx.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaCx.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaCx.kn0).
  { unfold know_ok, PbbaCx.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K54l K54r) | exact (conj K54l K54r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaCx.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaCx.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaCx.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaCx.ps0) with 0xafda8 in Hms. change (SR.ps_regs PbbaCx.ps0) with (map (fun i => (i, nth i PbbaCx.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaCx.ps0) with PbbaCx.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaCx.regs0 PbbaCx.regs_out0 72 KS_bbaCx KS_bbaCx_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaCx.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaCx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCx.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaCx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCx.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaCx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCx.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaCx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K54l K54r) | clear; lia].
Qed.

Module PbbaTe := BndP_Eb_011S9.LibSegEb_bbaTe.
Definition KS_bbaTe : list nat := Eval vm_compute in (BG.kept_list 72 PbbaTe.regs0 PbbaTe.regs_out0).
Lemma KS_bbaTe_ok : BG.kept_ok 72 PbbaTe.regs0 PbbaTe.regs_out0 KS_bbaTe = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaTe_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 65024 -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 69%nat) -> L5.u32_at RSEGS M (V 38%nat) (V 49%nat) -> 1 <= (V 49%nat) <= 64 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbad78 M) (st fx' R' 0xbb150 M')
        /\ (forall x, In x KS_bbaTe -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 49%nat)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat)
        /\ L5.defined M' ((V 47%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI22 K4 K5 pvzI23 K7 K8 K9 K10 K11 K12 K13 pvzI24 K15 K16 K17 K18 K19 pvzI25 K21 K22 K23 K24 K25 K26 K27 K28 pvzI26 K30 K31 K32 K33 K34 K35 pvzI27 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 pvzI28.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV49l; move HV49l before pvzI7; pose proof (proj2 pvzI7) as HV49r; move HV49r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV57l; move HV57l before pvzI9; pose proof (proj2 pvzI9) as HV57r; move HV57r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV58l; move HV58l before pvzI10; pose proof (proj2 pvzI10) as HV58r; move HV58r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV59l; move HV59l before pvzI11; pose proof (proj2 pvzI11) as HV59r; move HV59r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV60l; move HV60l before pvzI12; pose proof (proj2 pvzI12) as HV60r; move HV60r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV61l; move HV61l before pvzI13; pose proof (proj2 pvzI13) as HV61r; move HV61r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV62l; move HV62l before pvzI14; pose proof (proj2 pvzI14) as HV62r; move HV62r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV63l; move HV63l before pvzI15; pose proof (proj2 pvzI15) as HV63r; move HV63r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV64l; move HV64l before pvzI16; pose proof (proj2 pvzI16) as HV64r; move HV64r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV65l; move HV65l before pvzI17; pose proof (proj2 pvzI17) as HV65r; move HV65r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV66l; move HV66l before pvzI18; pose proof (proj2 pvzI18) as HV66r; move HV66r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV67l; move HV67l before pvzI19; pose proof (proj2 pvzI19) as HV67r; move HV67r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV68l; move HV68l before pvzI20; pose proof (proj2 pvzI20) as HV68r; move HV68r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV69l; move HV69l before pvzI21; pose proof (proj2 pvzI21) as HV69r; move HV69r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K3l; move K3l before pvzI22; pose proof (proj2 pvzI22) as K3r; move K3r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K6l; move K6l before pvzI23; pose proof (proj2 pvzI23) as K6r; move K6r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K14l; move K14l before pvzI24; pose proof (proj2 pvzI24) as K14r; move K14r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K20l; move K20l before pvzI25; pose proof (proj2 pvzI25) as K20r; move K20r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K29l; move K29l before pvzI26; pose proof (proj2 pvzI26) as K29r; move K29r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K36l; move K36l before pvzI27; pose proof (proj2 pvzI27) as K36r; move K36r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K66l; move K66l before pvzI28; pose proof (proj2 pvzI28) as K66r; move K66r before pvzI28; clear pvzI28.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E PbbaTe.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaTe.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaTe.kn0).
  { unfold know_ok, PbbaTe.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear - HV49l HV49r K66l K66r) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K66l K66r) | exact (conj K66l K66r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaTe.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaTe.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbbaTe.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K29l K29r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K36l K36r) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K36l K36r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaTe.ps0) with 0xbb150 in Hms. change (SR.ps_regs PbbaTe.ps0) with (map (fun i => (i, nth i PbbaTe.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaTe.ps0) with PbbaTe.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaTe.regs0 PbbaTe.regs_out0 72 KS_bbaTe KS_bbaTe_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTe.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbbaTe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbbaTf := BndP_Eb_011S9.LibSegEb_bbaTf.
Definition KS_bbaTf_0 : list nat := Eval vm_compute in (BG.kept_list 72 PbbaTf.regs0 PbbaTf.regs_out0).
Lemma KS_bbaTf_0_ok : BG.kept_ok 72 PbbaTf.regs0 PbbaTf.regs_out0 KS_bbaTf_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bbaTf_1 : list nat := Eval vm_compute in (BG.kept_list 72 PbbaTf.regs0 PbbaTf.regs_out1).
Lemma KS_bbaTf_1_ok : BG.kept_ok 72 PbbaTf.regs0 PbbaTf.regs_out1 KS_bbaTf_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaTf_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 65024 -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
  L5.u64_at RSEGS M ((V 36%nat) + 368) (V 53%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 376) (V 54%nat) -> 0 <= (V 53%nat) <= 140737488355328 -> 0 <= (V 54%nat) <= 140737488355328 ->
  L5.u32_at RSEGS M (V 38%nat) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 328) 16777216 -> 0 <= (V 50%nat) <= 16777216 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 116) <= bv_unsigned a < ((V 2%nat) - 116) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 116) <= i < ((V 2%nat) - 116) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xbad78 M) (st fx' R' 0xbc0c0 M')
        /\ (forall x, In x KS_bbaTf_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 766372
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 360)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 116)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 36%nat) + 368)
        /\ getr R' (reg 24) = Z_to_bv 64 ((((V 36%nat) + 368) / 8) + 2147450880)
        /\ (V 53%nat) < (V 54%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 116) 4
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat))
      \/ (msteps RSEGS (st fx R 0xbad78 M) (st fx' R' 0xbc26c M')
        /\ (forall x, In x KS_bbaTf_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 766408
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 36%nat) + 360)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 116)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 36%nat) + 368)
        /\ getr R' (reg 24) = Z_to_bv 64 ((((V 36%nat) + 368) / 8) + 2147450880)
        /\ (V 54%nat) <= (V 53%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 116) 4
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 K13 pvzI12 K15 K16 K17 K18 K19 pvzI13 K21 K22 K23 K24 K25 K26 K27 K28 pvzI14 K30 K31 K32 K33 K34 K35 pvzI15 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 pvzI16 pvzI17 K56 K57 pvzI18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV53l; move HV53l before pvzI8; pose proof (proj2 pvzI8) as HV53r; move HV53r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV54l; move HV54l before pvzI9; pose proof (proj2 pvzI9) as HV54r; move HV54r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K20l; move K20l before pvzI13; pose proof (proj2 pvzI13) as K20r; move K20r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K29l; move K29l before pvzI14; pose proof (proj2 pvzI14) as K29r; move K29r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K36l; move K36l before pvzI15; pose proof (proj2 pvzI15) as K36r; move K36r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K54l; move K54l before pvzI16; pose proof (proj2 pvzI16) as K54r; move K54r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K55l; move K55l before pvzI17; pose proof (proj2 pvzI17) as K55r; move K55r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K58l; move K58l before pvzI18; pose proof (proj2 pvzI18) as K58r; move K58r before pvzI18; clear pvzI18.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | 53%nat => vz_53 | 54%nat => vz_54 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PbbaTf.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaTf.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaTf.kn0).
  { unfold know_ok, PbbaTf.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear - HV53l HV53r K54l K54r) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear - HV54l HV54r K55l K55r) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K54l K54r) | exact (conj K54l K54r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV54l HV54r K55l K55r) | exact (conj K55l K55r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K58l K58r) | exact (conj K58l K58r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaTf.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaTf.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 116) <= bv_unsigned a < (vz_2 - 116) + 12) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaTf.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PbbaTf.ps0) with 0xbc0c0 in Hms. change (SR.ps_regs PbbaTf.ps0) with (map (fun i => (i, nth i PbbaTf.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbbaTf.ps0) with PbbaTf.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaTf.regs0 PbbaTf.regs_out0 72 KS_bbaTf_0 KS_bbaTf_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbbaTf.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaTf.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaTf.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaTf.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaTf.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaTf.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaTf.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaTf.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K58l K58r) | clear; lia].
  - right.
    change (SR.ps_pc PbbaTf.ps1) with 0xbc26c in Hms. change (SR.ps_regs PbbaTf.ps1) with (map (fun i => (i, nth i PbbaTf.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PbbaTf.ps1) with PbbaTf.cells1 in Hcells. unfold PbbaTf.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaTf.regs0 PbbaTf.regs_out1 72 KS_bbaTf_1 KS_bbaTf_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PbbaTf.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaTf.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaTf.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaTf.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaTf.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaTf.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaTf.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PbbaTf.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PbbaTf.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K58l K58r) | clear; lia].
Qed.

Module PbbaTx := BndP_Eb_012S9.LibSegEb_bbaTx.
Definition KS_bbaTx : list nat := Eval vm_compute in (BG.kept_list 72 PbbaTx.regs0 PbbaTx.regs_out0).
Lemma KS_bbaTx_ok : BG.kept_ok 72 PbbaTx.regs0 PbbaTx.regs_out0 KS_bbaTx = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaTx_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 65024 -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 24) -> getr R (reg 24) = Z_to_bv 64 1 -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
  L5.u32_at RSEGS M (V 38%nat) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 328) 16777216 -> 16777217 <= (V 50%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbad78 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_bbaTx -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 765372
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 13
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 pvzI11 K21 K22 K23 K24 K25 K26 K27 K28 pvzI12 K30 K31 K32 K33 K34 K35 pvzI13 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K20l; move K20l before pvzI11; pose proof (proj2 pvzI11) as K20r; move K20r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K29l; move K29l before pvzI12; pose proof (proj2 pvzI12) as K29r; move K29r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K36l; move K36l before pvzI13; pose proof (proj2 pvzI13) as K36r; move K36r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K54l; move K54l before pvzI14; pose proof (proj2 pvzI14) as K54r; move K54r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbbaTx.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaTx.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaTx.kn0).
  { unfold know_ok, PbbaTx.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K14l K14r; lia | clear - HV38l HV38r K14l K14r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K54l K54r) | exact (conj K54l K54r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaTx.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaTx.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaTx.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaTx.ps0) with 0xafda8 in Hms. change (SR.ps_regs PbbaTx.ps0) with (map (fun i => (i, nth i PbbaTx.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaTx.ps0) with PbbaTx.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaTx.regs0 PbbaTx.regs_out0 72 KS_bbaTx KS_bbaTx_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaTx.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaTx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTx.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaTx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTx.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaTx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTx.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaTx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K54l K54r) | clear; lia].
Qed.

Module PbbaCTc := BndP_Eb_010S9.LibSegEb_bbaCTc.
Definition KS_bbaCTc : list nat := Eval vm_compute in (BG.kept_list 72 PbbaCTc.regs0 PbbaCTc.regs_out0).
Lemma KS_bbaCTc_ok : BG.kept_ok 72 PbbaCTc.regs0 PbbaCTc.regs_out0 KS_bbaCTc = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaCTc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 53%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 36%nat) + 368) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 368) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 37%nat) -> L5.u64_at RSEGS M (V 37%nat) 1277312 -> L5KA.zeros_at M 2147610555 1 -> L5KA.zeros_at M 2147610546 1 ->
  L5.u8_at RSEGS M ((V 36%nat) + 16) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 50%nat) -> 0 <= (V 50%nat) <= 16777216 -> 4096 <= (V 53%nat) <= 140737488355296 ->
  aligned (V 53%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 368) <= bv_unsigned a < ((V 36%nat) + 368) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 368) <= i < ((V 36%nat) + 368) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbafb4 M) (st fx' R' 0xab900 M')
        /\ (forall x, In x KS_bbaCTc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 766068
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 702720
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 368) ((V 53%nat) + 32)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G18 G19 G20 G21 G22 G23 G25 G26 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 pvzI12 K21 K22 K23 K24 K25 K26 K27 K28 pvzI13 K30 K31 K32 K33 K34 K35 pvzI14 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 pvzI15 pvzI16 K60.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV53l; move HV53l before pvzI8; pose proof (proj2 pvzI8) as HV53r; move HV53r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K20l; move K20l before pvzI12; pose proof (proj2 pvzI12) as K20r; move K20r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K29l; move K29l before pvzI13; pose proof (proj2 pvzI13) as K29r; move K29r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K36l; move K36l before pvzI14; pose proof (proj2 pvzI14) as K36r; move K36r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K58l; move K58l before pvzI15; pose proof (proj2 pvzI15) as K58r; move K58r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K59l; move K59l before pvzI16; pose proof (proj2 pvzI16) as K59r; move K59r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbbaCTc.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaCTc.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaCTc.kn0).
  { unfold know_ok, PbbaCTc.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K54]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | byte_tac ltac:(clear) | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV50l HV50r K58l K58r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K58l K58r) | exact (conj K58l K58r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K59l K59r) | exact (conj K59l K59r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV53l HV53r K59l K59r) | clear; lia | exact K60]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaCTc.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaCTc.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 368) <= bv_unsigned a < (vz_36 + 368) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaCTc.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaCTc.ps0) with 0xab900 in Hms. change (SR.ps_regs PbbaCTc.ps0) with (map (fun i => (i, nth i PbbaCTc.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaCTc.ps0) with PbbaCTc.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaCTc.regs0 PbbaCTc.regs_out0 72 KS_bbaCTc KS_bbaCTc_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaCTc.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaCTc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCTc.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaCTc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCTc.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaCTc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCTc.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaCTc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCTc.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaCTc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCTc.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaCTc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCTc.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaCTc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K59l K59r) | clear; lia].
Qed.

Module PbbaCTs := BndP_Eb_010S9.LibSegEb_bbaCTs.
Definition KS_bbaCTs : list nat := Eval vm_compute in (BG.kept_list 72 PbbaCTs.regs0 PbbaCTs.regs_out0).
Lemma KS_bbaCTs_ok : BG.kept_ok 72 PbbaCTs.regs0 PbbaCTs.regs_out0 KS_bbaCTs = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaCTs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 53%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 36%nat) + 368) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 368) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 37%nat) -> L5.u64_at RSEGS M (V 37%nat) 1277312 -> L5KA.zeros_at M 2147610555 1 -> L5KA.zeros_at M 2147610546 1 ->
  L5.u8_at RSEGS M ((V 36%nat) + 16) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 50%nat) -> 0 <= (V 50%nat) <= 16777216 -> 4128 <= (V 55%nat) <= 140737488355328 ->
  aligned (V 55%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 368) <= bv_unsigned a < ((V 36%nat) + 368) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 368) <= i < ((V 36%nat) + 368) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbb008 M) (st fx' R' 0xab900 M')
        /\ (forall x, In x KS_bbaCTs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 766068
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 702720
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 368) (V 55%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G25 G26 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 K13 pvzI12 K15 K16 K17 K18 K19 pvzI13 K21 K22 K23 K24 K25 K26 K27 K28 pvzI14 K30 K31 K32 K33 K34 K35 pvzI15 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 pvzI16 pvzI17 K60.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV53l; move HV53l before pvzI8; pose proof (proj2 pvzI8) as HV53r; move HV53r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV55l; move HV55l before pvzI9; pose proof (proj2 pvzI9) as HV55r; move HV55r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K20l; move K20l before pvzI13; pose proof (proj2 pvzI13) as K20r; move K20r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K29l; move K29l before pvzI14; pose proof (proj2 pvzI14) as K29r; move K29r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K36l; move K36l before pvzI15; pose proof (proj2 pvzI15) as K36r; move K36r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K58l; move K58l before pvzI16; pose proof (proj2 pvzI16) as K58r; move K58r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K59l; move K59l before pvzI17; pose proof (proj2 pvzI17) as K59r; move K59r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_55 := V 55%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 53%nat => Z_to_bv 64 vz_53 | 55%nat => Z_to_bv 64 vz_55 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | 53%nat => vz_53 | 55%nat => vz_55 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 56%nat. }
  assert (HR: regs_ok E PbbaCTs.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaCTs.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaCTs.kn0).
  { unfold know_ok, PbbaCTs.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K54]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | byte_tac ltac:(clear) | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV50l HV50r K58l K58r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K58l K58r) | exact (conj K58l K58r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K59l K59r) | exact (conj K59l K59r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV55l HV55r K59l K59r) | clear; lia | exact K60]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaCTs.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaCTs.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 368) <= bv_unsigned a < (vz_36 + 368) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaCTs.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaCTs.ps0) with 0xab900 in Hms. change (SR.ps_regs PbbaCTs.ps0) with (map (fun i => (i, nth i PbbaCTs.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaCTs.ps0) with PbbaCTs.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaCTs.regs0 PbbaCTs.regs_out0 72 KS_bbaCTs KS_bbaCTs_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaCTs.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaCTs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCTs.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaCTs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCTs.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaCTs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCTs.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaCTs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCTs.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaCTs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCTs.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaCTs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaCTs.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaCTs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV55l HV55r K59l K59r) | clear; lia].
Qed.

Module PbbaITc := BndP_Eb_010S9.LibSegEb_bbaITc.
Definition KS_bbaITc : list nat := Eval vm_compute in (BG.kept_list 72 PbbaITc.regs0 PbbaITc.regs_out0).
Lemma KS_bbaITc_ok : BG.kept_ok 72 PbbaITc.regs0 PbbaITc.regs_out0 KS_bbaITc = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaITc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 53%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 36%nat) + 368) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 368) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 37%nat) -> L5.u64_at RSEGS M (V 37%nat) 1277312 -> L5KA.zeros_at M 2147610555 1 -> L5KA.zeros_at M 2147610546 1 ->
  L5.u8_at RSEGS M ((V 36%nat) + 16) 0 -> 4096 <= (V 53%nat) <= 140737488355296 -> aligned (V 53%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 368) <= bv_unsigned a < ((V 36%nat) + 368) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 368) <= i < ((V 36%nat) + 368) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbaea4 M) (st fx' R' 0xad238 M')
        /\ (forall x, In x KS_bbaITc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 765736
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 709176
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 368) ((V 53%nat) + 32)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G18 G19 G20 G21 G22 G23 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 pvzI11 K21 K22 K23 K24 K25 K26 K27 K28 pvzI12 K30 K31 K32 K33 K34 K35 pvzI13 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 pvzI14 K58.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV53l; move HV53l before pvzI7; pose proof (proj2 pvzI7) as HV53r; move HV53r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K20l; move K20l before pvzI11; pose proof (proj2 pvzI11) as K20r; move K20r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K29l; move K29l before pvzI12; pose proof (proj2 pvzI12) as K29r; move K29r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K36l; move K36l before pvzI13; pose proof (proj2 pvzI13) as K36r; move K36r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K57l; move K57l before pvzI14; pose proof (proj2 pvzI14) as K57r; move K57r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbbaITc.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaITc.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaITc.kn0).
  { unfold know_ok, PbbaITc.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K54]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | byte_tac ltac:(clear) | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K57l K57r) | exact (conj K57l K57r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV53l HV53r K57l K57r) | clear; lia | exact K58]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaITc.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaITc.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 368) <= bv_unsigned a < (vz_36 + 368) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaITc.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaITc.ps0) with 0xad238 in Hms. change (SR.ps_regs PbbaITc.ps0) with (map (fun i => (i, nth i PbbaITc.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaITc.ps0) with PbbaITc.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaITc.regs0 PbbaITc.regs_out0 72 KS_bbaITc KS_bbaITc_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaITc.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaITc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaITc.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaITc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaITc.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaITc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaITc.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaITc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaITc.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaITc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaITc.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaITc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K57l K57r) | clear; lia].
Qed.

Module PbbaITs := BndP_Eb_010S9.LibSegEb_bbaITs.
Definition KS_bbaITs : list nat := Eval vm_compute in (BG.kept_list 72 PbbaITs.regs0 PbbaITs.regs_out0).
Lemma KS_bbaITs_ok : BG.kept_ok 72 PbbaITs.regs0 PbbaITs.regs_out0 KS_bbaITs = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaITs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 53%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 36%nat) + 368) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 368) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 37%nat) -> L5.u64_at RSEGS M (V 37%nat) 1277312 -> L5KA.zeros_at M 2147610555 1 -> L5KA.zeros_at M 2147610546 1 ->
  L5.u8_at RSEGS M ((V 36%nat) + 16) 0 -> 4128 <= (V 55%nat) <= 140737488355328 -> aligned (V 55%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 368) <= bv_unsigned a < ((V 36%nat) + 368) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 368) <= i < ((V 36%nat) + 368) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbaec4 M) (st fx' R' 0xad238 M')
        /\ (forall x, In x KS_bbaITs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 765736
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 709176
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 368) (V 55%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G25 G26 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 pvzI12 K21 K22 K23 K24 K25 K26 K27 K28 pvzI13 K30 K31 K32 K33 K34 K35 pvzI14 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 pvzI15 K58.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV53l; move HV53l before pvzI7; pose proof (proj2 pvzI7) as HV53r; move HV53r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K20l; move K20l before pvzI12; pose proof (proj2 pvzI12) as K20r; move K20r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K29l; move K29l before pvzI13; pose proof (proj2 pvzI13) as K29r; move K29r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K36l; move K36l before pvzI14; pose proof (proj2 pvzI14) as K36r; move K36r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K57l; move K57l before pvzI15; pose proof (proj2 pvzI15) as K57r; move K57r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_55 := V 55%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 53%nat => Z_to_bv 64 vz_53 | 55%nat => Z_to_bv 64 vz_55 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 53%nat => vz_53 | 55%nat => vz_55 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 56%nat. }
  assert (HR: regs_ok E PbbaITs.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaITs.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaITs.kn0).
  { unfold know_ok, PbbaITs.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K54]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | byte_tac ltac:(clear) | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K57l K57r) | exact (conj K57l K57r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV55l HV55r K57l K57r) | clear; lia | exact K58]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaITs.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaITs.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 368) <= bv_unsigned a < (vz_36 + 368) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaITs.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaITs.ps0) with 0xad238 in Hms. change (SR.ps_regs PbbaITs.ps0) with (map (fun i => (i, nth i PbbaITs.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaITs.ps0) with PbbaITs.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaITs.regs0 PbbaITs.regs_out0 72 KS_bbaITs KS_bbaITs_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaITs.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaITs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaITs.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaITs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaITs.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaITs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaITs.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaITs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaITs.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaITs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaITs.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaITs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV55l HV55r K57l K57r) | clear; lia].
Qed.

Module PbbaTTc := BndP_Eb_011S9.LibSegEb_bbaTTc.
Definition KS_bbaTTc : list nat := Eval vm_compute in (BG.kept_list 72 PbbaTTc.regs0 PbbaTTc.regs_out0).
Lemma KS_bbaTTc_ok : BG.kept_ok 72 PbbaTTc.regs0 PbbaTTc.regs_out0 KS_bbaTTc = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaTTc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 53%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 368) -> getr R (reg 24) = Z_to_bv 64 ((((V 36%nat) + 368) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 37%nat) -> L5.u64_at RSEGS M (V 37%nat) 1277312 -> L5KA.zeros_at M 2147610555 1 -> L5KA.zeros_at M 2147610546 1 ->
  L5.u8_at RSEGS M ((V 36%nat) + 16) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 50%nat) -> 0 <= (V 50%nat) <= 16777216 -> 4096 <= (V 53%nat) <= 140737488355296 ->
  aligned (V 53%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 368) <= bv_unsigned a < ((V 36%nat) + 368) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 368) <= i < ((V 36%nat) + 368) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbb1a4 M) (st fx' R' 0xab900 M')
        /\ (forall x, In x KS_bbaTTc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 766516
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 702720
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 368) ((V 53%nat) + 32)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 pvzI12 K21 K22 K23 K24 K25 K26 K27 K28 pvzI13 K30 K31 K32 K33 K34 K35 pvzI14 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 pvzI15 pvzI16 K60.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV53l; move HV53l before pvzI8; pose proof (proj2 pvzI8) as HV53r; move HV53r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K20l; move K20l before pvzI12; pose proof (proj2 pvzI12) as K20r; move K20r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K29l; move K29l before pvzI13; pose proof (proj2 pvzI13) as K29r; move K29r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K36l; move K36l before pvzI14; pose proof (proj2 pvzI14) as K36r; move K36r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K58l; move K58l before pvzI15; pose proof (proj2 pvzI15) as K58r; move K58r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K59l; move K59l before pvzI16; pose proof (proj2 pvzI16) as K59r; move K59r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PbbaTTc.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaTTc.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaTTc.kn0).
  { unfold know_ok, PbbaTTc.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K54]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | byte_tac ltac:(clear) | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV50l HV50r K58l K58r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K58l K58r) | exact (conj K58l K58r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K59l K59r) | exact (conj K59l K59r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV53l HV53r K59l K59r) | clear; lia | exact K60]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaTTc.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaTTc.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 368) <= bv_unsigned a < (vz_36 + 368) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaTTc.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaTTc.ps0) with 0xab900 in Hms. change (SR.ps_regs PbbaTTc.ps0) with (map (fun i => (i, nth i PbbaTTc.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaTTc.ps0) with PbbaTTc.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaTTc.regs0 PbbaTTc.regs_out0 72 KS_bbaTTc KS_bbaTTc_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaTTc.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaTTc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTTc.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaTTc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTTc.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaTTc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTTc.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaTTc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTTc.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaTTc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTTc.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaTTc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTTc.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaTTc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV53l HV53r K59l K59r) | clear; lia].
Qed.

Module PbbaTTs := BndP_Eb_011S9.LibSegEb_bbaTTs.
Definition KS_bbaTTs : list nat := Eval vm_compute in (BG.kept_list 72 PbbaTTs.regs0 PbbaTTs.regs_out0).
Lemma KS_bbaTTs_ok : BG.kept_ok 72 PbbaTTs.regs0 PbbaTTs.regs_out0 KS_bbaTTs = true. Proof. vm_compute. reflexivity. Qed.
Lemma bbaTTs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 20) = Z_to_bv 64 (V 38%nat) -> getr R (reg 21) = Z_to_bv 64 (V 53%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 368) -> getr R (reg 24) = Z_to_bv 64 ((((V 36%nat) + 368) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 47%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 37%nat) -> L5.u64_at RSEGS M (V 37%nat) 1277312 -> L5KA.zeros_at M 2147610555 1 -> L5KA.zeros_at M 2147610546 1 ->
  L5.u8_at RSEGS M ((V 36%nat) + 16) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 50%nat) -> 0 <= (V 50%nat) <= 16777216 -> 4128 <= (V 55%nat) <= 140737488355328 ->
  aligned (V 55%nat) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 368) <= bv_unsigned a < ((V 36%nat) + 368) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 368) <= i < ((V 36%nat) + 368) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbb1c8 M) (st fx' R' 0xab900 M')
        /\ (forall x, In x KS_bbaTTs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 766516
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 702720
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 368) (V 55%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 K12 K13 pvzI12 K15 K16 K17 K18 K19 pvzI13 K21 K22 K23 K24 K25 K26 K27 K28 pvzI14 K30 K31 K32 K33 K34 K35 pvzI15 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 pvzI16 pvzI17 K60.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV53l; move HV53l before pvzI8; pose proof (proj2 pvzI8) as HV53r; move HV53r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV55l; move HV55l before pvzI9; pose proof (proj2 pvzI9) as HV55r; move HV55r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K14l; move K14l before pvzI12; pose proof (proj2 pvzI12) as K14r; move K14r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K20l; move K20l before pvzI13; pose proof (proj2 pvzI13) as K20r; move K20r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K29l; move K29l before pvzI14; pose proof (proj2 pvzI14) as K29r; move K29r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K36l; move K36l before pvzI15; pose proof (proj2 pvzI15) as K36r; move K36r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K58l; move K58l before pvzI16; pose proof (proj2 pvzI16) as K58r; move K58r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K59l; move K59l before pvzI17; pose proof (proj2 pvzI17) as K59r; move K59r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_55 := V 55%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 53%nat => Z_to_bv 64 vz_53 | 55%nat => Z_to_bv 64 vz_55 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | 53%nat => vz_53 | 55%nat => vz_55 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 56%nat. }
  assert (HR: regs_ok E PbbaTTs.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbbaTTs.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbbaTTs.kn0).
  { unfold know_ok, PbbaTTs.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K20l K20r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K20l K20r; lia | clear - HV37l HV37r K20l K20r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K54]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | byte_tac ltac:(clear) | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV50l HV50r K58l K58r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K58l K58r) | exact (conj K58l K58r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K59l K59r) | exact (conj K59l K59r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV55l HV55r K59l K59r) | clear; lia | exact K60]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbbaTTs.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbbaTTs.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 368) <= bv_unsigned a < (vz_36 + 368) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbbaTTs.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbbaTTs.ps0) with 0xab900 in Hms. change (SR.ps_regs PbbaTTs.ps0) with (map (fun i => (i, nth i PbbaTTs.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbbaTTs.ps0) with PbbaTTs.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbbaTTs.regs0 PbbaTTs.regs_out0 72 KS_bbaTTs KS_bbaTTs_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbbaTTs.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbbaTTs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTTs.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbbaTTs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTTs.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbbaTTs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTTs.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbbaTTs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTTs.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbbaTTs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTTs.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbbaTTs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbbaTTs.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbbaTTs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV55l HV55r K59l K59r) | clear; lia].
Qed.

End PEBBAP2.
