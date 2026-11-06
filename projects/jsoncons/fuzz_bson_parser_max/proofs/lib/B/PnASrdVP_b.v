(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BigLinkZA.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan. From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b. From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_asvA_b LibSegBa_asvH1_b LibSegBa_asvH0_b LibSegBa_asvR_b LibSegBa_asvQ_b LibSegBa_asvE_b LibSegBa_asvF_b LibSegBa_asvD_b LibSegBa_asvD2_b LibSegBa_asvD3_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMASRVP.
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
Module PasvA := LibSegBa_asvA_b.
Definition KS_asvA_0 : list nat := Eval vm_compute in (BG.kept_list 70 PasvA.regs0 PasvA.regs_out0).
Lemma KS_asvA_0_ok : BG.kept_ok 70 PasvA.regs0 PasvA.regs_out0 KS_asvA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_asvA_1 : list nat := Eval vm_compute in (BG.kept_list 70 PasvA.regs0 PasvA.regs_out1).
Lemma KS_asvA_1_ok : BG.kept_ok 70 PasvA.regs0 PasvA.regs_out1 KS_asvA_1 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma asvA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 (V 38%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 ->
  L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) -> 0 <= (V 38%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5500 M) (st fx' R' 0xb55a0 M')
        /\ (forall x, In x KS_asvA_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 144)
        /\ getr R' (reg 8) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + 256) / 8)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) + 256)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + 272)
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 37%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((((V 36%nat) + 256) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 36%nat) + 256)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 37%nat) + 8)
        /\ 1 <= (((V 38%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0xb5500 M) (st fx' R' 0xb570c M')
        /\ (forall x, In x KS_asvA_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ (((V 38%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
  intros [pos2 fit2] [pos36 fit36] [pos37 fit37] [pos38 fit38] x2 x10 x11 x12 noimg q_g1309752 d_g1309760 rg2 al2 wr_sl160 rg36 al36 dsh36 shz36
         wr_at36 dsp36 rg37 al37 dsh37 shz37 wr_at37 dsp37 d36_37 rg38.
  pose (E := Env (fun n => if Nat.eqb n 2 then Z_to_bv 64 (V 2%nat) else reg_ev R (fun k => Z_to_bv 64 (V k)) n) (fun _ => [])).
  pose (VZ := fun j : nat => match j with
    | 2%nat => V 2%nat | 36%nat => V 36%nat | 37%nat => V 37%nat | 38%nat => V 38%nat | _ => bv_unsigned (ev E j) end).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ j) by BigLinkZA.za_tac VZ 39%nat.
  assert (SLOTS : regs_ok E PasvA.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. cbn [PasvA.regs0 tl BG.slots].
    repeat match goal with |- _ /\ _ => split end; [ .. | exact I]; slotP ZA. }
  assert (KNOWN : know_ok RSEGS E M PasvA.kn0).
  { unfold know_ok, PasvA.kn0. repeat apply Forall_cons; [ .. | apply Forall_nil].
    all: lazymatch goal with
    | |- kentry_ok _ _ _ (KImg _ _) => apply L5K.kentry_KImg; [lia | lia | exact noimg]
    | |- kentry_ok _ _ _ (KRange _ _ _) => eapply L5K.kentry_KRange; [evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KAlign _ _) =>
        eapply L5K.kentry_KAlign; [evalEk ZA zfacts | lia | match goal with Al : aligned _ _ |- _ => exact Al end]
    | |- kentry_ok _ _ _ (KDisj _ _ _ _) =>
        eapply L5K.kentry_KDisj; [evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KWr _ _) =>
        eapply L5K.kentry_KWr; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                               | match goal with W : L5.writable _ _ _ _ |- _ => exactA W end]
    | |- kentry_ok _ _ _ (KUnk _ _) =>
        eapply L5K.kentry_KUnk; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                | match goal with Df : L5.defined _ _ _ |- _ => exactA Df end]
    | |- kentry_ok _ _ _ (KZero _ _) =>
        eapply L5KA.kentry_KZero; [evalEk ZA zfacts | evalEk ZA zfacts | zfacts; lia | lia | zfacts; lia
                                  | match goal with Z0 : L5KA.zeros_at _ _ _ |- _ => exactA Z0 end]
    | |- kentry_ok _ _ _ (KWord _ 8 _) =>
        eapply L5K.kentry_KWord8; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with Q : L5.u64_at _ _ _ _ |- _ => exactA Q end]
    | |- kentry_ok _ _ _ (KWord _ 4 _) =>
        eapply L5K.kentry_KWord4; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with D : L5.u32_at _ _ _ _ |- _ => exactA D end]
    | |- kentry_ok _ _ _ (KWord _ 1 _) =>
        eapply L5K.kentry_KWord1; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                  | match goal with B : L5.u8_at _ _ _ _ |- _ => exactA B end]
    end. }
  destruct (PasvA.seg_sound_ax fx E R M SLOTS KNOWN (Forall_nil _))
    as (fx1 & E1 & R1 & M1 & pick & post & PICK & AG & RUN & OUTR & _ & _ & FRAME & CELLS & GROW).
  unfold PasvA.PSS, PasvA.SXALL in PICK. cbn [app map] in PICK.
  exists fx1, R1, M1. split; [exact GROW|].
  split; [intros a OUT; apply FRAME; eapply L5K.outside_cons_e; [evalEk' ZA AG zfacts | evalEk' ZA AG zfacts | lia | apply L5K.outside_nil_e]|].
  split; [intros i Ri OUT; apply FRAME; eapply L5K.outside_cons_e; [evalEk' ZA AG zfacts | evalEk' ZA AG zfacts | rewrite BG.unsigned_lit by lia; lia | apply L5K.outside_nil_e]|].
  destruct pick as [|[|pick]]; cbn [nth_error] in PICK; [ .. | destruct pick; cbn in PICK; discriminate];
    injection PICK as PICK; subst post.
  - left. split; [exact RUN|].
    split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvA.regs0 PasvA.regs_out0 70 KS_asvA_0 KS_asvA_0_ok SLOTS AG OUTR x IN)|].
    assert (CK : Forall (kentry_ok RSEGS E1 M1) PasvA.cells0) by (apply Forall_forall; exact CELLS).
    unfold PasvA.cells0 in CK.
    repeat (apply Forall_cons_iff in CK; let c := fresh "cell" in destruct CK as [c CK]).
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- getr _ (reg ?i) = _ =>
        rewrite (BG.out_reg PasvA.regs_out0 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
    | |- L5.u64_at _ _ (?sp - ?k) ?v =>
        match goal with C : kentry_ok _ _ _ (KWord (SA (EVar 2) ?off) 8 ?e) |- _ =>
          let same_slot := constr:(eq_refl : off = Z.opp k) in
          apply (u64_of_KWord8a E1 M1 (EVar 2) off e sp v _ C); [evalEk' ZA AG zfacts | evalEk' ZA AG zfacts | lia]
        end
    | |- ?c <= ?T =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    end.
  - right. split; [exact RUN|].
    split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvA.regs0 PasvA.regs_out1 70 KS_asvA_1 KS_asvA_1_ok SLOTS AG OUTR x IN)|].
    assert (CK : Forall (kentry_ok RSEGS E1 M1) PasvA.cells1) by (apply Forall_forall; exact CELLS).
    unfold PasvA.cells1 in CK.
    repeat (apply Forall_cons_iff in CK; let c := fresh "cell" in destruct CK as [c CK]).
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- getr _ (reg ?i) = _ =>
        rewrite (BG.out_reg PasvA.regs_out1 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
    | |- L5.u64_at _ _ (?sp - ?k) ?v =>
        match goal with C : kentry_ok _ _ _ (KWord (SA (EVar 2) ?off) 8 ?e) |- _ =>
          let same_slot := constr:(eq_refl : off = Z.opp k) in
          apply (u64_of_KWord8a E1 M1 (EVar 2) off e sp v _ C); [evalEk' ZA AG zfacts | evalEk' ZA AG zfacts | lia]
        end
    | |- ?T < ?c =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    end.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasvH1 := LibSegBa_asvH1_b.
Definition KS_asvH1_0 : list nat := Eval vm_compute in (BG.kept_list 70 PasvH1.regs0 PasvH1.regs_out0).
Lemma KS_asvH1_0_ok : BG.kept_ok 70 PasvH1.regs0 PasvH1.regs_out0 KS_asvH1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_asvH1_1 : list nat := Eval vm_compute in (BG.kept_list 70 PasvH1.regs0 PasvH1.regs_out1).
Lemma KS_asvH1_1_ok : BG.kept_ok 70 PasvH1.regs0 PasvH1.regs_out1 KS_asvH1_1 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma asvH1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 ((((V 37%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 25) = Z_to_bv 64 (V 39%nat) -> getr R (reg 26) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 36%nat) + 256) -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) -> 1 <= (V 33%nat) <= 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> 1 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb55a0 M) (st fx' R' 0xb55e0 M')
        /\ (forall x, In x KS_asvH1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 742820
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 2147450880
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 (V 39%nat)
        /\ (V 39%nat) < 16384
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 742820
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 54%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 56%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 57%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 58%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 59%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 60%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 37%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((((V 36%nat) + 256) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 36%nat) + 256))
      \/ (msteps RSEGS (st fx R 0xb55a0 M) (st fx' R' 0xb55e0 M')
        /\ (forall x, In x KS_asvH1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 742820
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 2147450880
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 16384
        /\ 16384 <= (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 742820
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 54%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 56%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 57%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 58%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 59%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 60%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 37%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((((V 36%nat) + 256) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 36%nat) + 256))).
Proof.
  intros [pos2 fit2] [pos33 fit33] [pos36 fit36] [pos37 fit37] [pos38 fit38] [pos39 fit39] [pos48 fit48] [pos49 fit49] [pos50 fit50] [pos51 fit51]
         [pos52 fit52] [pos53 fit53] [pos54 fit54] [pos55 fit55] [pos56 fit56] [pos57 fit57] [pos58 fit58] [pos59 fit59] [pos60 fit60] x2 x8 x9 x10
         x18 x19 x20 x21 x25 x26 x27 noimg q_g1309752 d_g1309760 rg2 al2 wr_sl160 q_sl8 q_sl16 q_sl24 q_sl32 q_sl40 q_sl48 q_sl56 q_sl64 q_sl72
         q_sl80 q_sl88 q_sl96 q_sl104 q_sl136 q_sl128 q_sl120 q_sl112 rg36 al36 dsh36 shz36 wr_at36 dsp36 rg37 al37 dsh37 shz37 wr_at37 dsp37 d36_37
         q_at36_288 rg33 q_at36_272 rg39.
  pose (E := Env (fun n => if Nat.eqb n 2 then Z_to_bv 64 (V 2%nat) else reg_ev R (fun k => Z_to_bv 64 (V k)) n) (fun _ => [])).
  pose (VZ := fun j : nat => match j with
    | 2%nat => V 2%nat | 33%nat => V 33%nat | 36%nat => V 36%nat | 37%nat => V 37%nat | 38%nat => V 38%nat | 39%nat => V 39%nat | 48%nat => V 48%nat
    | 49%nat => V 49%nat | 50%nat => V 50%nat | 51%nat => V 51%nat | 52%nat => V 52%nat | 53%nat => V 53%nat | 54%nat => V 54%nat
    | 55%nat => V 55%nat | 56%nat => V 56%nat | 57%nat => V 57%nat | 58%nat => V 58%nat | 59%nat => V 59%nat | 60%nat => V 60%nat
    | _ => bv_unsigned (ev E j) end).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ j) by BigLinkZA.za_tac VZ 61%nat.
  assert (SLOTS : regs_ok E PasvH1.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. cbn [PasvH1.regs0 tl BG.slots].
    repeat match goal with |- _ /\ _ => split end; [ .. | exact I]; slotP ZA. }
  assert (KNOWN : know_ok RSEGS E M PasvH1.kn0).
  { unfold know_ok, PasvH1.kn0. repeat apply Forall_cons; [ .. | apply Forall_nil].
    all: lazymatch goal with
    | |- kentry_ok _ _ _ (KImg _ _) => apply L5K.kentry_KImg; [lia | lia | exact noimg]
    | |- kentry_ok _ _ _ (KRange _ _ _) => eapply L5K.kentry_KRange; [evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KAlign _ _) =>
        eapply L5K.kentry_KAlign; [evalEk ZA zfacts | lia | match goal with Al : aligned _ _ |- _ => exact Al end]
    | |- kentry_ok _ _ _ (KDisj _ _ _ _) =>
        eapply L5K.kentry_KDisj; [evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KWr _ _) =>
        eapply L5K.kentry_KWr; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                               | match goal with W : L5.writable _ _ _ _ |- _ => exactA W end]
    | |- kentry_ok _ _ _ (KUnk _ _) =>
        eapply L5K.kentry_KUnk; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                | match goal with Df : L5.defined _ _ _ |- _ => exactA Df end]
    | |- kentry_ok _ _ _ (KZero _ _) =>
        eapply L5KA.kentry_KZero; [evalEk ZA zfacts | evalEk ZA zfacts | zfacts; lia | lia | zfacts; lia
                                  | match goal with Z0 : L5KA.zeros_at _ _ _ |- _ => exactA Z0 end]
    | |- kentry_ok _ _ _ (KWord _ 8 _) =>
        eapply L5K.kentry_KWord8; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with Q : L5.u64_at _ _ _ _ |- _ => exactA Q end]
    | |- kentry_ok _ _ _ (KWord _ 4 _) =>
        eapply L5K.kentry_KWord4; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with D : L5.u32_at _ _ _ _ |- _ => exactA D end]
    | |- kentry_ok _ _ _ (KWord _ 1 _) =>
        eapply L5K.kentry_KWord1; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                  | match goal with B : L5.u8_at _ _ _ _ |- _ => exactA B end]
    end. }
  destruct (PasvH1.seg_sound_ax fx E R M SLOTS KNOWN (Forall_nil _))
    as (fx1 & E1 & R1 & M1 & pick & post & PICK & AG & RUN & OUTR & _ & _ & FRAME & CELLS & GROW).
  unfold PasvH1.PSS, PasvH1.SXALL in PICK. cbn [app map] in PICK.
  exists fx1, R1, M1. split; [exact GROW|].
  split; [intros a OUT; apply FRAME; eapply L5K.outside_cons_e; [evalEk' ZA AG zfacts | evalEk' ZA AG zfacts | lia | apply L5K.outside_nil_e]|].
  split; [intros i Ri OUT; apply FRAME; eapply L5K.outside_cons_e; [evalEk' ZA AG zfacts | evalEk' ZA AG zfacts | rewrite BG.unsigned_lit by lia; lia | apply L5K.outside_nil_e]|].
  destruct pick as [|[|pick]]; cbn [nth_error] in PICK; [ .. | destruct pick; cbn in PICK; discriminate];
    injection PICK as PICK; subst post.
  - left. split; [exact RUN|].
    split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvH1.regs0 PasvH1.regs_out0 70 KS_asvH1_0 KS_asvH1_0_ok SLOTS AG OUTR x IN)|].
    assert (CK : Forall (kentry_ok RSEGS E1 M1) PasvH1.cells0) by (apply Forall_forall; exact CELLS).
    unfold PasvH1.cells0 in CK.
    repeat (apply Forall_cons_iff in CK; let c := fresh "cell" in destruct CK as [c CK]).
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- getr _ (reg ?i) = _ =>
        rewrite (BG.out_reg PasvH1.regs_out0 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
    | |- L5.u64_at _ _ (?sp - ?k) ?v =>
        match goal with C : kentry_ok _ _ _ (KWord (SA (EVar 2) ?off) 8 ?e) |- _ =>
          let same_slot := constr:(eq_refl : off = Z.opp k) in
          apply (u64_of_KWord8a E1 M1 (EVar 2) off e sp v _ C); [evalEk' ZA AG zfacts | evalEk' ZA AG zfacts | lia]
        end
    | |- ?T < ?c =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    end.
  - right. split; [exact RUN|].
    split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvH1.regs0 PasvH1.regs_out1 70 KS_asvH1_1 KS_asvH1_1_ok SLOTS AG OUTR x IN)|].
    assert (CK : Forall (kentry_ok RSEGS E1 M1) PasvH1.cells1) by (apply Forall_forall; exact CELLS).
    unfold PasvH1.cells1 in CK.
    repeat (apply Forall_cons_iff in CK; let c := fresh "cell" in destruct CK as [c CK]).
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- getr _ (reg ?i) = _ =>
        rewrite (BG.out_reg PasvH1.regs_out1 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
    | |- L5.u64_at _ _ (?sp - ?k) ?v =>
        match goal with C : kentry_ok _ _ _ (KWord (SA (EVar 2) ?off) 8 ?e) |- _ =>
          let same_slot := constr:(eq_refl : off = Z.opp k) in
          apply (u64_of_KWord8a E1 M1 (EVar 2) off e sp v _ C); [evalEk' ZA AG zfacts | evalEk' ZA AG zfacts | lia]
        end
    | |- ?c <= ?T =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    end.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasvH0 := LibSegBa_asvH0_b.
Definition KS_asvH0_0 : list nat := Eval vm_compute in (BG.kept_list 70 PasvH0.regs0 PasvH0.regs_out0).
Lemma KS_asvH0_0_ok : BG.kept_ok 70 PasvH0.regs0 PasvH0.regs_out0 KS_asvH0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_asvH0_1 : list nat := Eval vm_compute in (BG.kept_list 70 PasvH0.regs0 PasvH0.regs_out1).
Lemma KS_asvH0_1_ok : BG.kept_ok 70 PasvH0.regs0 PasvH0.regs_out1 KS_asvH0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_asvH0_2 : list nat := Eval vm_compute in (BG.kept_list 70 PasvH0.regs0 PasvH0.regs_out2).
Lemma KS_asvH0_2_ok : BG.kept_ok 70 PasvH0.regs0 PasvH0.regs_out2 KS_asvH0_2 = true. Proof. vm_compute. reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma asvH0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 ((((V 37%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 25) = Z_to_bv 64 (V 39%nat) -> getr R (reg 26) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 36%nat) + 256) -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> 6905856 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 45%nat) \/ (V 45%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 45%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 45%nat) 272 -> (((V 2%nat) - 160) + 160 <= (V 45%nat) \/ (V 45%nat) + 272 <= ((V 2%nat) - 160)) ->
  ((V 36%nat) + 296 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) -> ((V 37%nat) + 24 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 37%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 45%nat) -> L5.u64_at RSEGS M (V 45%nat) 1265968 ->
  L5.u8_at RSEGS M ((V 45%nat) + 152) (V 62%nat) -> 0 <= (V 62%nat) <= 2 -> L5KA.zeros_at M 2147609123 1 -> 1 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb55a0 M) (st fx' R' 0xb55e0 M')
        /\ (forall x, In x KS_asvH0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 742820
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 2147450880
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 (V 39%nat)
        /\ (V 39%nat) < 16384
        /\ (((((4611686018427387904 * (V 62%nat)) mod 2 ^ 64) / 9223372036854775808) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 742820
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 54%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 56%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 57%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 58%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 59%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 60%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 37%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((((V 36%nat) + 256) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 36%nat) + 256))
      \/ (msteps RSEGS (st fx R 0xb55a0 M) (st fx' R' 0xb5644 M')
        /\ (forall x, In x KS_asvH0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 742820
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 2147450880
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 16384
        /\ 16384 <= (V 39%nat)
        /\ (((((4611686018427387904 * (V 62%nat)) mod 2 ^ 64) / 9223372036854775808) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 742820
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 54%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 56%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 57%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 58%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 59%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 60%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 37%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((((V 36%nat) + 256) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 36%nat) + 256))
      \/ (msteps RSEGS (st fx R 0xb55a0 M) (st fx' R' 0xb570c M')
        /\ (forall x, In x KS_asvH0_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 38%nat) - (V 39%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 2147450880
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 60%nat)
        /\ 1 <= (((((4611686018427387904 * (V 62%nat)) mod 2 ^ 64) / 9223372036854775808) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 742820
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 54%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 55%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 56%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 57%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 58%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 59%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 60%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 37%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((((V 36%nat) + 256) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 36%nat) + 256))).
Proof.
  intros [pos2 fit2] [pos36 fit36] [pos37 fit37] [pos38 fit38] [pos39 fit39] [pos45 fit45] [pos48 fit48] [pos49 fit49] [pos50 fit50] [pos51 fit51]
         [pos52 fit52] [pos53 fit53] [pos54 fit54] [pos55 fit55] [pos56 fit56] [pos57 fit57] [pos58 fit58] [pos59 fit59] [pos60 fit60] [pos62 fit62]
         x2 x8 x9 x10 x18 x19 x20 x21 x25 x26 x27 noimg q_g1309752 d_g1309760 rg2 al2 wr_sl160 q_sl8 q_sl16 q_sl24 q_sl32 q_sl40 q_sl48 q_sl56 q_sl64
         q_sl72 q_sl80 q_sl88 q_sl96 q_sl104 q_sl136 q_sl128 q_sl120 q_sl112 rg36 al36 dsh36 shz36 wr_at36 dsp36 rg37 al37 dsh37 shz37 wr_at37 dsp37
         d36_37 q_at36_288 q_at36_272 rg45 al45 dsh45 shz45 wr_at45 dsp45 d36_45 d37_45 q_at36_240 q_at45 b_at45_152 rg62 zs_g2147609123 rg39.
  pose (E := Env (fun n => if Nat.eqb n 2 then Z_to_bv 64 (V 2%nat) else reg_ev R (fun k => Z_to_bv 64 (V k)) n) (fun _ => [])).
  pose (VZ := fun j : nat => match j with
    | 2%nat => V 2%nat | 36%nat => V 36%nat | 37%nat => V 37%nat | 38%nat => V 38%nat | 39%nat => V 39%nat | 45%nat => V 45%nat | 48%nat => V 48%nat
    | 49%nat => V 49%nat | 50%nat => V 50%nat | 51%nat => V 51%nat | 52%nat => V 52%nat | 53%nat => V 53%nat | 54%nat => V 54%nat
    | 55%nat => V 55%nat | 56%nat => V 56%nat | 57%nat => V 57%nat | 58%nat => V 58%nat | 59%nat => V 59%nat | 60%nat => V 60%nat
    | 62%nat => V 62%nat | _ => bv_unsigned (ev E j) end).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ j) by BigLinkZA.za_tac VZ 63%nat.
  assert (SLOTS : regs_ok E PasvH0.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. cbn [PasvH0.regs0 tl BG.slots].
    repeat match goal with |- _ /\ _ => split end; [ .. | exact I]; slotP ZA. }
  assert (KNOWN : know_ok RSEGS E M PasvH0.kn0).
  { unfold know_ok, PasvH0.kn0. repeat apply Forall_cons; [ .. | apply Forall_nil].
    all: lazymatch goal with
    | |- kentry_ok _ _ _ (KImg _ _) => apply L5K.kentry_KImg; [lia | lia | exact noimg]
    | |- kentry_ok _ _ _ (KRange _ _ _) => eapply L5K.kentry_KRange; [evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KAlign _ _) =>
        eapply L5K.kentry_KAlign; [evalEk ZA zfacts | lia | match goal with Al : aligned _ _ |- _ => exact Al end]
    | |- kentry_ok _ _ _ (KDisj _ _ _ _) =>
        eapply L5K.kentry_KDisj; [evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KWr _ _) =>
        eapply L5K.kentry_KWr; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                               | match goal with W : L5.writable _ _ _ _ |- _ => exactA W end]
    | |- kentry_ok _ _ _ (KUnk _ _) =>
        eapply L5K.kentry_KUnk; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                | match goal with Df : L5.defined _ _ _ |- _ => exactA Df end]
    | |- kentry_ok _ _ _ (KZero _ _) =>
        eapply L5KA.kentry_KZero; [evalEk ZA zfacts | evalEk ZA zfacts | zfacts; lia | lia | zfacts; lia
                                  | match goal with Z0 : L5KA.zeros_at _ _ _ |- _ => exactA Z0 end]
    | |- kentry_ok _ _ _ (KWord _ 8 _) =>
        eapply L5K.kentry_KWord8; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with Q : L5.u64_at _ _ _ _ |- _ => exactA Q end]
    | |- kentry_ok _ _ _ (KWord _ 4 _) =>
        eapply L5K.kentry_KWord4; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with D : L5.u32_at _ _ _ _ |- _ => exactA D end]
    | |- kentry_ok _ _ _ (KWord _ 1 _) =>
        eapply L5K.kentry_KWord1; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                  | match goal with B : L5.u8_at _ _ _ _ |- _ => exactA B end]
    end. }
  destruct (PasvH0.seg_sound_ax fx E R M SLOTS KNOWN (Forall_nil _))
    as (fx1 & E1 & R1 & M1 & pick & post & PICK & AG & RUN & OUTR & _ & _ & FRAME & CELLS & GROW).
  unfold PasvH0.PSS, PasvH0.SXALL in PICK. cbn [app map] in PICK.
  exists fx1, R1, M1. split; [exact GROW|].
  split; [intros a OUT; apply FRAME; eapply L5K.outside_cons_e; [evalEk' ZA AG zfacts | evalEk' ZA AG zfacts | lia | apply L5K.outside_nil_e]|].
  split; [intros i Ri OUT; apply FRAME; eapply L5K.outside_cons_e; [evalEk' ZA AG zfacts | evalEk' ZA AG zfacts | rewrite BG.unsigned_lit by lia; lia | apply L5K.outside_nil_e]|].
  destruct pick as [|[|[|pick]]]; cbn [nth_error] in PICK; [ .. | destruct pick; cbn in PICK; discriminate];
    injection PICK as PICK; subst post.
  - left. split; [exact RUN|].
    split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvH0.regs0 PasvH0.regs_out0 70 KS_asvH0_0 KS_asvH0_0_ok SLOTS AG OUTR x IN)|].
    assert (CK : Forall (kentry_ok RSEGS E1 M1) PasvH0.cells0) by (apply Forall_forall; exact CELLS).
    unfold PasvH0.cells0 in CK.
    repeat (apply Forall_cons_iff in CK; let c := fresh "cell" in destruct CK as [c CK]).
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- getr _ (reg ?i) = _ =>
        rewrite (BG.out_reg PasvH0.regs_out0 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
    | |- L5.u64_at _ _ (?sp - ?k) ?v =>
        match goal with C : kentry_ok _ _ _ (KWord (SA (EVar 2) ?off) 8 ?e) |- _ =>
          let same_slot := constr:(eq_refl : off = Z.opp k) in
          apply (u64_of_KWord8a E1 M1 (EVar 2) off e sp v _ C); [evalEk' ZA AG zfacts | evalEk' ZA AG zfacts | lia]
        end
    | |- ?T < ?c =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    end.
  - right; left. split; [exact RUN|].
    split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvH0.regs0 PasvH0.regs_out1 70 KS_asvH0_1 KS_asvH0_1_ok SLOTS AG OUTR x IN)|].
    assert (CK : Forall (kentry_ok RSEGS E1 M1) PasvH0.cells1) by (apply Forall_forall; exact CELLS).
    unfold PasvH0.cells1 in CK.
    repeat (apply Forall_cons_iff in CK; let c := fresh "cell" in destruct CK as [c CK]).
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- getr _ (reg ?i) = _ =>
        rewrite (BG.out_reg PasvH0.regs_out1 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
    | |- L5.u64_at _ _ (?sp - ?k) ?v =>
        match goal with C : kentry_ok _ _ _ (KWord (SA (EVar 2) ?off) 8 ?e) |- _ =>
          let same_slot := constr:(eq_refl : off = Z.opp k) in
          apply (u64_of_KWord8a E1 M1 (EVar 2) off e sp v _ C); [evalEk' ZA AG zfacts | evalEk' ZA AG zfacts | lia]
        end
    | |- ?T < ?c =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    | |- ?c <= ?T =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    end.
  - right; right. split; [exact RUN|].
    split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvH0.regs0 PasvH0.regs_out2 70 KS_asvH0_2 KS_asvH0_2_ok SLOTS AG OUTR x IN)|].
    assert (CK : Forall (kentry_ok RSEGS E1 M1) PasvH0.cells2) by (apply Forall_forall; exact CELLS).
    unfold PasvH0.cells2 in CK.
    repeat (apply Forall_cons_iff in CK; let c := fresh "cell" in destruct CK as [c CK]).
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- getr _ (reg ?i) = _ =>
        rewrite (BG.out_reg PasvH0.regs_out2 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
    | |- L5.u64_at _ _ (?sp - ?k) ?v =>
        match goal with C : kentry_ok _ _ _ (KWord (SA (EVar 2) ?off) 8 ?e) |- _ =>
          let same_slot := constr:(eq_refl : off = Z.opp k) in
          apply (u64_of_KWord8a E1 M1 (EVar 2) off e sp v _ C); [evalEk' ZA AG zfacts | evalEk' ZA AG zfacts | lia]
        end
    | |- ?c <= ?T =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    end.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasvR := LibSegBa_asvR_b.
Definition KS_asvR : list nat := Eval vm_compute in (BG.kept_list 70 PasvR.regs0 PasvR.regs_out0).
Lemma KS_asvR_ok : BG.kept_ok 70 PasvR.regs0 PasvR.regs_out0 KS_asvR = true. Proof. vm_compute. reflexivity. Qed.
Lemma asvR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 ((((V 37%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 23) = Z_to_bv 64 (V 43%nat) -> getr R (reg 25) = Z_to_bv 64 (V 39%nat) -> getr R (reg 26) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 36%nat) + 256) -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u64_at RSEGS M (V 37%nat) (V 40%nat) -> L5.u64_at RSEGS M ((V 37%nat) + 8) ((V 40%nat) + (V 41%nat)) -> 0 <= (V 40%nat) <= 140737488355328 -> 0 <= (V 41%nat) <= 134217728 ->
  1 <= (V 43%nat) <= 16384 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb55e0 M) (st fx' R' 0xb5764 M')
        /\ (forall x, In x KS_asvR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 742920
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 41%nat) + (V 43%nat))
        /\ getr R' (reg 22) = Z_to_bv 64 (V 41%nat)).
Proof.
  intros [pos2 fit2] [pos36 fit36] [pos37 fit37] [pos38 fit38] [pos39 fit39] [pos40 fit40] [pos41 fit41] [pos43 fit43] [pos48 fit48] [pos49 fit49]
         [pos50 fit50] [pos51 fit51] [pos52 fit52] [pos53 fit53] [pos54 fit54] [pos55 fit55] [pos56 fit56] [pos57 fit57] [pos58 fit58] [pos59 fit59]
         [pos60 fit60] x2 x8 x9 x18 x19 x20 x21 x23 x25 x26 x27 noimg q_g1309752 d_g1309760 rg2 al2 wr_sl160 q_sl8 q_sl16 q_sl24 q_sl32 q_sl40 q_sl48
         q_sl56 q_sl64 q_sl72 q_sl80 q_sl88 q_sl96 q_sl104 q_sl136 q_sl128 q_sl120 q_sl112 rg36 al36 dsh36 shz36 wr_at36 dsp36 rg37 al37 dsh37 shz37
         wr_at37 dsp37 d36_37 q_at37 q_at37_8 rg40 rg41 rg43.
  pose (E := Env (fun n => if Nat.eqb n 2 then Z_to_bv 64 (V 2%nat) else reg_ev R (fun k => Z_to_bv 64 (V k)) n) (fun _ => [])).
  pose (VZ := fun j : nat => match j with
    | 2%nat => V 2%nat | 36%nat => V 36%nat | 37%nat => V 37%nat | 38%nat => V 38%nat | 39%nat => V 39%nat | 40%nat => V 40%nat | 41%nat => V 41%nat
    | 43%nat => V 43%nat | 48%nat => V 48%nat | 49%nat => V 49%nat | 50%nat => V 50%nat | 51%nat => V 51%nat | 52%nat => V 52%nat
    | 53%nat => V 53%nat | 54%nat => V 54%nat | 55%nat => V 55%nat | 56%nat => V 56%nat | 57%nat => V 57%nat | 58%nat => V 58%nat
    | 59%nat => V 59%nat | 60%nat => V 60%nat | _ => bv_unsigned (ev E j) end).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ j) by BigLinkZA.za_tac VZ 61%nat.
  assert (SLOTS : regs_ok E PasvR.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. cbn [PasvR.regs0 tl BG.slots].
    repeat match goal with |- _ /\ _ => split end; [ .. | exact I]; slotP ZA. }
  assert (KNOWN : know_ok RSEGS E M PasvR.kn0).
  { unfold know_ok, PasvR.kn0. repeat apply Forall_cons; [ .. | apply Forall_nil].
    all: lazymatch goal with
    | |- kentry_ok _ _ _ (KImg _ _) => apply L5K.kentry_KImg; [lia | lia | exact noimg]
    | |- kentry_ok _ _ _ (KRange _ _ _) => eapply L5K.kentry_KRange; [evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KAlign _ _) =>
        eapply L5K.kentry_KAlign; [evalEk ZA zfacts | lia | match goal with Al : aligned _ _ |- _ => exact Al end]
    | |- kentry_ok _ _ _ (KDisj _ _ _ _) =>
        eapply L5K.kentry_KDisj; [evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KWr _ _) =>
        eapply L5K.kentry_KWr; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                               | match goal with W : L5.writable _ _ _ _ |- _ => exactA W end]
    | |- kentry_ok _ _ _ (KUnk _ _) =>
        eapply L5K.kentry_KUnk; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                | match goal with Df : L5.defined _ _ _ |- _ => exactA Df end]
    | |- kentry_ok _ _ _ (KZero _ _) =>
        eapply L5KA.kentry_KZero; [evalEk ZA zfacts | evalEk ZA zfacts | zfacts; lia | lia | zfacts; lia
                                  | match goal with Z0 : L5KA.zeros_at _ _ _ |- _ => exactA Z0 end]
    | |- kentry_ok _ _ _ (KWord _ 8 _) =>
        eapply L5K.kentry_KWord8; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with Q : L5.u64_at _ _ _ _ |- _ => exactA Q end]
    | |- kentry_ok _ _ _ (KWord _ 4 _) =>
        eapply L5K.kentry_KWord4; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with D : L5.u32_at _ _ _ _ |- _ => exactA D end]
    | |- kentry_ok _ _ _ (KWord _ 1 _) =>
        eapply L5K.kentry_KWord1; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                  | match goal with B : L5.u8_at _ _ _ _ |- _ => exactA B end]
    end. }
  destruct (PasvR.seg_sound_ax fx E R M SLOTS KNOWN (Forall_nil _))
    as (fx1 & E1 & R1 & M1 & pick & post & PICK & AG & RUN & OUTR & _ & _ & FRAME & CELLS & GROW).
  unfold PasvR.PSS, PasvR.SXALL in PICK. cbn [app map] in PICK.
  exists fx1, R1, M1. split; [exact GROW|].
  split; [intros a; apply FRAME, L5K.outside_nil_e|]. split; [intros i _; apply FRAME, L5K.outside_nil_e|].
  apply L5K.nth_error_single in PICK. subst post.
  split; [exact RUN|].
  split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvR.regs0 PasvR.regs_out0 70 KS_asvR KS_asvR_ok SLOTS AG OUTR x IN)|].
  repeat match goal with |- _ /\ _ => split end.
  all: lazymatch goal with
  | |- getr _ (reg ?i) = _ =>
      rewrite (BG.out_reg PasvR.regs_out0 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
  end.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasvQ := LibSegBa_asvQ_b.
Definition KS_asvQ : list nat := Eval vm_compute in (BG.kept_list 70 PasvQ.regs0 PasvQ.regs_out0).
Lemma KS_asvQ_ok : BG.kept_ok 70 PasvQ.regs0 PasvQ.regs_out0 KS_asvQ = true. Proof. vm_compute. reflexivity. Qed.
Lemma asvQ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 ((((V 37%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 22) = Z_to_bv 64 (V 46%nat) -> getr R (reg 23) = Z_to_bv 64 (V 43%nat) -> getr R (reg 25) = Z_to_bv 64 (V 39%nat) -> getr R (reg 26) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 36%nat) + 256) -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u64_at RSEGS M (V 37%nat) (V 42%nat) -> 4096 <= (V 42%nat) <= 140737488355328 -> 0 <= (V 46%nat) <= 134217728 -> 1 <= (V 43%nat) <= 16384 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5608 M) (st fx' R' 0xaed4c M')
        /\ (forall x, In x KS_asvQ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 742960
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + (V 46%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)).
Proof.
  intros [pos2 fit2] [pos36 fit36] [pos37 fit37] [pos38 fit38] [pos39 fit39] [pos42 fit42] [pos43 fit43] [pos46 fit46] [pos48 fit48] [pos49 fit49]
         [pos50 fit50] [pos51 fit51] [pos52 fit52] [pos53 fit53] [pos54 fit54] [pos55 fit55] [pos56 fit56] [pos57 fit57] [pos58 fit58] [pos59 fit59]
         [pos60 fit60] x2 x8 x9 x18 x19 x20 x21 x22 x23 x25 x26 x27 noimg q_g1309752 d_g1309760 rg2 al2 wr_sl160 q_sl8 q_sl16 q_sl24 q_sl32 q_sl40
         q_sl48 q_sl56 q_sl64 q_sl72 q_sl80 q_sl88 q_sl96 q_sl104 q_sl136 q_sl128 q_sl120 q_sl112 rg36 al36 dsh36 shz36 wr_at36 dsp36 rg37 al37 dsh37
         shz37 wr_at37 dsp37 d36_37 q_at37 rg42 rg46 rg43.
  pose (E := Env (fun n => if Nat.eqb n 2 then Z_to_bv 64 (V 2%nat) else reg_ev R (fun k => Z_to_bv 64 (V k)) n) (fun _ => [])).
  pose (VZ := fun j : nat => match j with
    | 2%nat => V 2%nat | 36%nat => V 36%nat | 37%nat => V 37%nat | 38%nat => V 38%nat | 39%nat => V 39%nat | 42%nat => V 42%nat | 43%nat => V 43%nat
    | 46%nat => V 46%nat | 48%nat => V 48%nat | 49%nat => V 49%nat | 50%nat => V 50%nat | 51%nat => V 51%nat | 52%nat => V 52%nat
    | 53%nat => V 53%nat | 54%nat => V 54%nat | 55%nat => V 55%nat | 56%nat => V 56%nat | 57%nat => V 57%nat | 58%nat => V 58%nat
    | 59%nat => V 59%nat | 60%nat => V 60%nat | _ => bv_unsigned (ev E j) end).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ j) by BigLinkZA.za_tac VZ 61%nat.
  assert (SLOTS : regs_ok E PasvQ.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. cbn [PasvQ.regs0 tl BG.slots].
    repeat match goal with |- _ /\ _ => split end; [ .. | exact I]; slotP ZA. }
  assert (KNOWN : know_ok RSEGS E M PasvQ.kn0).
  { unfold know_ok, PasvQ.kn0. repeat apply Forall_cons; [ .. | apply Forall_nil].
    all: lazymatch goal with
    | |- kentry_ok _ _ _ (KImg _ _) => apply L5K.kentry_KImg; [lia | lia | exact noimg]
    | |- kentry_ok _ _ _ (KRange _ _ _) => eapply L5K.kentry_KRange; [evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KAlign _ _) =>
        eapply L5K.kentry_KAlign; [evalEk ZA zfacts | lia | match goal with Al : aligned _ _ |- _ => exact Al end]
    | |- kentry_ok _ _ _ (KDisj _ _ _ _) =>
        eapply L5K.kentry_KDisj; [evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KWr _ _) =>
        eapply L5K.kentry_KWr; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                               | match goal with W : L5.writable _ _ _ _ |- _ => exactA W end]
    | |- kentry_ok _ _ _ (KUnk _ _) =>
        eapply L5K.kentry_KUnk; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                | match goal with Df : L5.defined _ _ _ |- _ => exactA Df end]
    | |- kentry_ok _ _ _ (KZero _ _) =>
        eapply L5KA.kentry_KZero; [evalEk ZA zfacts | evalEk ZA zfacts | zfacts; lia | lia | zfacts; lia
                                  | match goal with Z0 : L5KA.zeros_at _ _ _ |- _ => exactA Z0 end]
    | |- kentry_ok _ _ _ (KWord _ 8 _) =>
        eapply L5K.kentry_KWord8; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with Q : L5.u64_at _ _ _ _ |- _ => exactA Q end]
    | |- kentry_ok _ _ _ (KWord _ 4 _) =>
        eapply L5K.kentry_KWord4; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with D : L5.u32_at _ _ _ _ |- _ => exactA D end]
    | |- kentry_ok _ _ _ (KWord _ 1 _) =>
        eapply L5K.kentry_KWord1; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                  | match goal with B : L5.u8_at _ _ _ _ |- _ => exactA B end]
    end. }
  destruct (PasvQ.seg_sound_ax fx E R M SLOTS KNOWN (Forall_nil _))
    as (fx1 & E1 & R1 & M1 & pick & post & PICK & AG & RUN & OUTR & _ & _ & FRAME & CELLS & GROW).
  unfold PasvQ.PSS, PasvQ.SXALL in PICK. cbn [app map] in PICK.
  exists fx1, R1, M1. split; [exact GROW|].
  split; [intros a; apply FRAME, L5K.outside_nil_e|]. split; [intros i _; apply FRAME, L5K.outside_nil_e|].
  apply L5K.nth_error_single in PICK. subst post.
  split; [exact RUN|].
  split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvQ.regs0 PasvQ.regs_out0 70 KS_asvQ KS_asvQ_ok SLOTS AG OUTR x IN)|].
  repeat match goal with |- _ /\ _ => split end.
  all: lazymatch goal with
  | |- getr _ (reg ?i) = _ =>
      rewrite (BG.out_reg PasvQ.regs_out0 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
  end.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasvE := LibSegBa_asvE_b.
Definition KS_asvE_0 : list nat := Eval vm_compute in (BG.kept_list 70 PasvE.regs0 PasvE.regs_out0).
Lemma KS_asvE_0_ok : BG.kept_ok 70 PasvE.regs0 PasvE.regs_out0 KS_asvE_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_asvE_1 : list nat := Eval vm_compute in (BG.kept_list 70 PasvE.regs0 PasvE.regs_out1).
Lemma KS_asvE_1_ok : BG.kept_ok 70 PasvE.regs0 PasvE.regs_out1 KS_asvE_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_asvE_2 : list nat := Eval vm_compute in (BG.kept_list 70 PasvE.regs0 PasvE.regs_out2).
Lemma KS_asvE_2_ok : BG.kept_ok 70 PasvE.regs0 PasvE.regs_out2 KS_asvE_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma asvE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 10) = Z_to_bv 64 (V 44%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 ((((V 37%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 22) = Z_to_bv 64 (V 46%nat) -> getr R (reg 23) = Z_to_bv 64 (V 43%nat) -> getr R (reg 25) = Z_to_bv 64 (V 39%nat) -> getr R (reg 26) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 36%nat) + 256) -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  1 <= (V 43%nat) <= 16384 -> 0 <= (V 44%nat) <= 16384 -> 0 <= (V 46%nat) <= 134217728 -> 1 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5630 M) (st fx' R' 0xb5764 M')
        /\ (forall x, In x KS_asvE_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 743108
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 44%nat) + (V 46%nat))
        /\ getr R' (reg 24) = Z_to_bv 64 (V 44%nat)
        /\ 1 <= (((V 44%nat) - (V 43%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb5630 M) (st fx' R' 0xb55a0 M')
        /\ (forall x, In x KS_asvE_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 39%nat) - (V 44%nat))
        /\ 1 <= (((((V 39%nat) + ((18446744073709551615 * (V 44%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64)
        /\ (((V 44%nat) - (V 43%nat)) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb5630 M) (st fx' R' 0xb570c M')
        /\ (forall x, In x KS_asvE_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 38%nat) + (((-1) * (V 39%nat)) + (V 44%nat)))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 60%nat)
        /\ (((((V 39%nat) + ((18446744073709551615 * (V 44%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ (((V 44%nat) - (V 43%nat)) mod 2 ^ 64) < 1)).
Proof.
  intros [pos2 fit2] [pos36 fit36] [pos37 fit37] [pos38 fit38] [pos39 fit39] [pos43 fit43] [pos44 fit44] [pos46 fit46] [pos48 fit48] [pos49 fit49]
         [pos50 fit50] [pos51 fit51] [pos52 fit52] [pos53 fit53] [pos54 fit54] [pos55 fit55] [pos56 fit56] [pos57 fit57] [pos58 fit58] [pos59 fit59]
         [pos60 fit60] x2 x8 x9 x10 x18 x19 x20 x21 x22 x23 x25 x26 x27 noimg q_g1309752 d_g1309760 rg2 al2 wr_sl160 q_sl8 q_sl16 q_sl24 q_sl32
         q_sl40 q_sl48 q_sl56 q_sl64 q_sl72 q_sl80 q_sl88 q_sl96 q_sl104 q_sl136 q_sl128 q_sl120 q_sl112 rg36 al36 dsh36 shz36 wr_at36 dsp36 rg37
         al37 dsh37 shz37 wr_at37 dsp37 d36_37 rg43 rg44 rg46 rg39.
  pose (E := Env (fun n => if Nat.eqb n 2 then Z_to_bv 64 (V 2%nat) else reg_ev R (fun k => Z_to_bv 64 (V k)) n) (fun _ => [])).
  pose (VZ := fun j : nat => match j with
    | 2%nat => V 2%nat | 36%nat => V 36%nat | 37%nat => V 37%nat | 38%nat => V 38%nat | 39%nat => V 39%nat | 43%nat => V 43%nat | 44%nat => V 44%nat
    | 46%nat => V 46%nat | 48%nat => V 48%nat | 49%nat => V 49%nat | 50%nat => V 50%nat | 51%nat => V 51%nat | 52%nat => V 52%nat
    | 53%nat => V 53%nat | 54%nat => V 54%nat | 55%nat => V 55%nat | 56%nat => V 56%nat | 57%nat => V 57%nat | 58%nat => V 58%nat
    | 59%nat => V 59%nat | 60%nat => V 60%nat | _ => bv_unsigned (ev E j) end).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ j) by BigLinkZA.za_tac VZ 61%nat.
  assert (SLOTS : regs_ok E PasvE.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. cbn [PasvE.regs0 tl BG.slots].
    repeat match goal with |- _ /\ _ => split end; [ .. | exact I]; slotP ZA. }
  assert (KNOWN : know_ok RSEGS E M PasvE.kn0).
  { unfold know_ok, PasvE.kn0. repeat apply Forall_cons; [ .. | apply Forall_nil].
    all: lazymatch goal with
    | |- kentry_ok _ _ _ (KImg _ _) => apply L5K.kentry_KImg; [lia | lia | exact noimg]
    | |- kentry_ok _ _ _ (KRange _ _ _) => eapply L5K.kentry_KRange; [evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KAlign _ _) =>
        eapply L5K.kentry_KAlign; [evalEk ZA zfacts | lia | match goal with Al : aligned _ _ |- _ => exact Al end]
    | |- kentry_ok _ _ _ (KDisj _ _ _ _) =>
        eapply L5K.kentry_KDisj; [evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KWr _ _) =>
        eapply L5K.kentry_KWr; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                               | match goal with W : L5.writable _ _ _ _ |- _ => exactA W end]
    | |- kentry_ok _ _ _ (KUnk _ _) =>
        eapply L5K.kentry_KUnk; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                | match goal with Df : L5.defined _ _ _ |- _ => exactA Df end]
    | |- kentry_ok _ _ _ (KZero _ _) =>
        eapply L5KA.kentry_KZero; [evalEk ZA zfacts | evalEk ZA zfacts | zfacts; lia | lia | zfacts; lia
                                  | match goal with Z0 : L5KA.zeros_at _ _ _ |- _ => exactA Z0 end]
    | |- kentry_ok _ _ _ (KWord _ 8 _) =>
        eapply L5K.kentry_KWord8; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with Q : L5.u64_at _ _ _ _ |- _ => exactA Q end]
    | |- kentry_ok _ _ _ (KWord _ 4 _) =>
        eapply L5K.kentry_KWord4; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with D : L5.u32_at _ _ _ _ |- _ => exactA D end]
    | |- kentry_ok _ _ _ (KWord _ 1 _) =>
        eapply L5K.kentry_KWord1; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                  | match goal with B : L5.u8_at _ _ _ _ |- _ => exactA B end]
    end. }
  destruct (PasvE.seg_sound_ax fx E R M SLOTS KNOWN (Forall_nil _))
    as (fx1 & E1 & R1 & M1 & pick & post & PICK & AG & RUN & OUTR & _ & _ & FRAME & CELLS & GROW).
  unfold PasvE.PSS, PasvE.SXALL in PICK. cbn [app map] in PICK.
  exists fx1, R1, M1. split; [exact GROW|].
  split; [intros a; apply FRAME, L5K.outside_nil_e|]. split; [intros i _; apply FRAME, L5K.outside_nil_e|].
  destruct pick as [|[|[|pick]]]; cbn [nth_error] in PICK; [ .. | destruct pick; cbn in PICK; discriminate];
    injection PICK as PICK; subst post.
  - left. split; [exact RUN|].
    split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvE.regs0 PasvE.regs_out0 70 KS_asvE_0 KS_asvE_0_ok SLOTS AG OUTR x IN)|].
    assert (CK : Forall (kentry_ok RSEGS E1 M1) PasvE.cells0) by (apply Forall_forall; exact CELLS).
    unfold PasvE.cells0 in CK.
    repeat (apply Forall_cons_iff in CK; let c := fresh "cell" in destruct CK as [c CK]).
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- getr _ (reg ?i) = _ =>
        rewrite (BG.out_reg PasvE.regs_out0 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
    | |- ?c <= ?T =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    end.
  - right; left. split; [exact RUN|].
    split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvE.regs0 PasvE.regs_out1 70 KS_asvE_1 KS_asvE_1_ok SLOTS AG OUTR x IN)|].
    assert (CK : Forall (kentry_ok RSEGS E1 M1) PasvE.cells1) by (apply Forall_forall; exact CELLS).
    unfold PasvE.cells1 in CK.
    repeat (apply Forall_cons_iff in CK; let c := fresh "cell" in destruct CK as [c CK]).
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- getr _ (reg ?i) = _ =>
        rewrite (BG.out_reg PasvE.regs_out1 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
    | |- ?T < ?c =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    | |- ?c <= ?T =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    end.
  - right; right. split; [exact RUN|].
    split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvE.regs0 PasvE.regs_out2 70 KS_asvE_2 KS_asvE_2_ok SLOTS AG OUTR x IN)|].
    assert (CK : Forall (kentry_ok RSEGS E1 M1) PasvE.cells2) by (apply Forall_forall; exact CELLS).
    unfold PasvE.cells2 in CK.
    repeat (apply Forall_cons_iff in CK; let c := fresh "cell" in destruct CK as [c CK]).
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- getr _ (reg ?i) = _ =>
        rewrite (BG.out_reg PasvE.regs_out2 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
    | |- ?T < ?c =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    end.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasvF := LibSegBa_asvF_b.
Definition KS_asvF_0 : list nat := Eval vm_compute in (BG.kept_list 70 PasvF.regs0 PasvF.regs_out0).
Lemma KS_asvF_0_ok : BG.kept_ok 70 PasvF.regs0 PasvF.regs_out0 KS_asvF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_asvF_1 : list nat := Eval vm_compute in (BG.kept_list 70 PasvF.regs0 PasvF.regs_out1).
Lemma KS_asvF_1_ok : BG.kept_ok 70 PasvF.regs0 PasvF.regs_out1 KS_asvF_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma asvF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 ((((V 37%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 24) = Z_to_bv 64 (V 44%nat) -> getr R (reg 25) = Z_to_bv 64 (V 39%nat) -> getr R (reg 26) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 36%nat) + 256) -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  0 <= (V 44%nat) <= 16384 -> 1 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb56c4 M) (st fx' R' 0xb55a0 M')
        /\ (forall x, In x KS_asvF_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 39%nat) - (V 44%nat))
        /\ 1 <= (((((V 39%nat) + ((18446744073709551615 * (V 44%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb56c4 M) (st fx' R' 0xb570c M')
        /\ (forall x, In x KS_asvF_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 38%nat) + (((-1) * (V 39%nat)) + (V 44%nat)))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 60%nat)
        /\ (((((V 39%nat) + ((18446744073709551615 * (V 44%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1)).
Proof.
  intros [pos2 fit2] [pos36 fit36] [pos37 fit37] [pos38 fit38] [pos39 fit39] [pos44 fit44] [pos48 fit48] [pos49 fit49] [pos50 fit50] [pos51 fit51]
         [pos52 fit52] [pos53 fit53] [pos54 fit54] [pos55 fit55] [pos56 fit56] [pos57 fit57] [pos58 fit58] [pos59 fit59] [pos60 fit60] x2 x8 x9 x18
         x19 x20 x21 x24 x25 x26 x27 noimg q_g1309752 d_g1309760 rg2 al2 wr_sl160 q_sl8 q_sl16 q_sl24 q_sl32 q_sl40 q_sl48 q_sl56 q_sl64 q_sl72
         q_sl80 q_sl88 q_sl96 q_sl104 q_sl136 q_sl128 q_sl120 q_sl112 rg36 al36 dsh36 shz36 wr_at36 dsp36 rg37 al37 dsh37 shz37 wr_at37 dsp37 d36_37
         rg44 rg39.
  pose (E := Env (fun n => if Nat.eqb n 2 then Z_to_bv 64 (V 2%nat) else reg_ev R (fun k => Z_to_bv 64 (V k)) n) (fun _ => [])).
  pose (VZ := fun j : nat => match j with
    | 2%nat => V 2%nat | 36%nat => V 36%nat | 37%nat => V 37%nat | 38%nat => V 38%nat | 39%nat => V 39%nat | 44%nat => V 44%nat | 48%nat => V 48%nat
    | 49%nat => V 49%nat | 50%nat => V 50%nat | 51%nat => V 51%nat | 52%nat => V 52%nat | 53%nat => V 53%nat | 54%nat => V 54%nat
    | 55%nat => V 55%nat | 56%nat => V 56%nat | 57%nat => V 57%nat | 58%nat => V 58%nat | 59%nat => V 59%nat | 60%nat => V 60%nat
    | _ => bv_unsigned (ev E j) end).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ j) by BigLinkZA.za_tac VZ 61%nat.
  assert (SLOTS : regs_ok E PasvF.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. cbn [PasvF.regs0 tl BG.slots].
    repeat match goal with |- _ /\ _ => split end; [ .. | exact I]; slotP ZA. }
  assert (KNOWN : know_ok RSEGS E M PasvF.kn0).
  { unfold know_ok, PasvF.kn0. repeat apply Forall_cons; [ .. | apply Forall_nil].
    all: lazymatch goal with
    | |- kentry_ok _ _ _ (KImg _ _) => apply L5K.kentry_KImg; [lia | lia | exact noimg]
    | |- kentry_ok _ _ _ (KRange _ _ _) => eapply L5K.kentry_KRange; [evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KAlign _ _) =>
        eapply L5K.kentry_KAlign; [evalEk ZA zfacts | lia | match goal with Al : aligned _ _ |- _ => exact Al end]
    | |- kentry_ok _ _ _ (KDisj _ _ _ _) =>
        eapply L5K.kentry_KDisj; [evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KWr _ _) =>
        eapply L5K.kentry_KWr; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                               | match goal with W : L5.writable _ _ _ _ |- _ => exactA W end]
    | |- kentry_ok _ _ _ (KUnk _ _) =>
        eapply L5K.kentry_KUnk; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                | match goal with Df : L5.defined _ _ _ |- _ => exactA Df end]
    | |- kentry_ok _ _ _ (KZero _ _) =>
        eapply L5KA.kentry_KZero; [evalEk ZA zfacts | evalEk ZA zfacts | zfacts; lia | lia | zfacts; lia
                                  | match goal with Z0 : L5KA.zeros_at _ _ _ |- _ => exactA Z0 end]
    | |- kentry_ok _ _ _ (KWord _ 8 _) =>
        eapply L5K.kentry_KWord8; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with Q : L5.u64_at _ _ _ _ |- _ => exactA Q end]
    | |- kentry_ok _ _ _ (KWord _ 4 _) =>
        eapply L5K.kentry_KWord4; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with D : L5.u32_at _ _ _ _ |- _ => exactA D end]
    | |- kentry_ok _ _ _ (KWord _ 1 _) =>
        eapply L5K.kentry_KWord1; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                  | match goal with B : L5.u8_at _ _ _ _ |- _ => exactA B end]
    end. }
  destruct (PasvF.seg_sound_ax fx E R M SLOTS KNOWN (Forall_nil _))
    as (fx1 & E1 & R1 & M1 & pick & post & PICK & AG & RUN & OUTR & _ & _ & FRAME & CELLS & GROW).
  unfold PasvF.PSS, PasvF.SXALL in PICK. cbn [app map] in PICK.
  exists fx1, R1, M1. split; [exact GROW|].
  split; [intros a; apply FRAME, L5K.outside_nil_e|]. split; [intros i _; apply FRAME, L5K.outside_nil_e|].
  destruct pick as [|[|pick]]; cbn [nth_error] in PICK; [ .. | destruct pick; cbn in PICK; discriminate];
    injection PICK as PICK; subst post.
  - left. split; [exact RUN|].
    split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvF.regs0 PasvF.regs_out0 70 KS_asvF_0 KS_asvF_0_ok SLOTS AG OUTR x IN)|].
    assert (CK : Forall (kentry_ok RSEGS E1 M1) PasvF.cells0) by (apply Forall_forall; exact CELLS).
    unfold PasvF.cells0 in CK.
    repeat (apply Forall_cons_iff in CK; let c := fresh "cell" in destruct CK as [c CK]).
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- getr _ (reg ?i) = _ =>
        rewrite (BG.out_reg PasvF.regs_out0 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
    | |- ?c <= ?T =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    end.
  - right. split; [exact RUN|].
    split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvF.regs0 PasvF.regs_out1 70 KS_asvF_1 KS_asvF_1_ok SLOTS AG OUTR x IN)|].
    assert (CK : Forall (kentry_ok RSEGS E1 M1) PasvF.cells1) by (apply Forall_forall; exact CELLS).
    unfold PasvF.cells1 in CK.
    repeat (apply Forall_cons_iff in CK; let c := fresh "cell" in destruct CK as [c CK]).
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- getr _ (reg ?i) = _ =>
        rewrite (BG.out_reg PasvF.regs_out1 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
    | |- ?T < ?c =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    end.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasvD := LibSegBa_asvD_b.
Definition KS_asvD : list nat := Eval vm_compute in (BG.kept_list 70 PasvD.regs0 PasvD.regs_out0).
Lemma KS_asvD_ok : BG.kept_ok 70 PasvD.regs0 PasvD.regs_out0 KS_asvD = true. Proof. vm_compute. reflexivity. Qed.
Lemma asvD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 ((((V 37%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 23) = Z_to_bv 64 16384 -> getr R (reg 25) = Z_to_bv 64 (V 39%nat) -> getr R (reg 26) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 36%nat) + 256) -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u64_at RSEGS M (V 37%nat) (V 40%nat) -> L5.u64_at RSEGS M ((V 37%nat) + 8) ((V 40%nat) + (V 41%nat)) -> 0 <= (V 40%nat) <= 140737488355328 -> 0 <= (V 41%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5644 M) (st fx' R' 0xb5764 M')
        /\ (forall x, In x KS_asvD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 743020
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 41%nat) + 16384)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 41%nat)).
Proof.
  intros [pos2 fit2] [pos36 fit36] [pos37 fit37] [pos38 fit38] [pos39 fit39] [pos40 fit40] [pos41 fit41] [pos48 fit48] [pos49 fit49] [pos50 fit50]
         [pos51 fit51] [pos52 fit52] [pos53 fit53] [pos54 fit54] [pos55 fit55] [pos56 fit56] [pos57 fit57] [pos58 fit58] [pos59 fit59] [pos60 fit60]
         x2 x8 x9 x18 x19 x20 x21 x23 x25 x26 x27 noimg q_g1309752 d_g1309760 rg2 al2 wr_sl160 q_sl8 q_sl16 q_sl24 q_sl32 q_sl40 q_sl48 q_sl56 q_sl64
         q_sl72 q_sl80 q_sl88 q_sl96 q_sl104 q_sl136 q_sl128 q_sl120 q_sl112 rg36 al36 dsh36 shz36 wr_at36 dsp36 rg37 al37 dsh37 shz37 wr_at37 dsp37
         d36_37 q_at37 q_at37_8 rg40 rg41.
  pose (E := Env (fun n => if Nat.eqb n 2 then Z_to_bv 64 (V 2%nat) else reg_ev R (fun k => Z_to_bv 64 (V k)) n) (fun _ => [])).
  pose (VZ := fun j : nat => match j with
    | 2%nat => V 2%nat | 36%nat => V 36%nat | 37%nat => V 37%nat | 38%nat => V 38%nat | 39%nat => V 39%nat | 40%nat => V 40%nat | 41%nat => V 41%nat
    | 48%nat => V 48%nat | 49%nat => V 49%nat | 50%nat => V 50%nat | 51%nat => V 51%nat | 52%nat => V 52%nat | 53%nat => V 53%nat
    | 54%nat => V 54%nat | 55%nat => V 55%nat | 56%nat => V 56%nat | 57%nat => V 57%nat | 58%nat => V 58%nat | 59%nat => V 59%nat
    | 60%nat => V 60%nat | _ => bv_unsigned (ev E j) end).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ j) by BigLinkZA.za_tac VZ 61%nat.
  assert (SLOTS : regs_ok E PasvD.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. cbn [PasvD.regs0 tl BG.slots].
    repeat match goal with |- _ /\ _ => split end; [ .. | exact I]; slotP ZA. }
  assert (KNOWN : know_ok RSEGS E M PasvD.kn0).
  { unfold know_ok, PasvD.kn0. repeat apply Forall_cons; [ .. | apply Forall_nil].
    all: lazymatch goal with
    | |- kentry_ok _ _ _ (KImg _ _) => apply L5K.kentry_KImg; [lia | lia | exact noimg]
    | |- kentry_ok _ _ _ (KRange _ _ _) => eapply L5K.kentry_KRange; [evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KAlign _ _) =>
        eapply L5K.kentry_KAlign; [evalEk ZA zfacts | lia | match goal with Al : aligned _ _ |- _ => exact Al end]
    | |- kentry_ok _ _ _ (KDisj _ _ _ _) =>
        eapply L5K.kentry_KDisj; [evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KWr _ _) =>
        eapply L5K.kentry_KWr; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                               | match goal with W : L5.writable _ _ _ _ |- _ => exactA W end]
    | |- kentry_ok _ _ _ (KUnk _ _) =>
        eapply L5K.kentry_KUnk; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                | match goal with Df : L5.defined _ _ _ |- _ => exactA Df end]
    | |- kentry_ok _ _ _ (KZero _ _) =>
        eapply L5KA.kentry_KZero; [evalEk ZA zfacts | evalEk ZA zfacts | zfacts; lia | lia | zfacts; lia
                                  | match goal with Z0 : L5KA.zeros_at _ _ _ |- _ => exactA Z0 end]
    | |- kentry_ok _ _ _ (KWord _ 8 _) =>
        eapply L5K.kentry_KWord8; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with Q : L5.u64_at _ _ _ _ |- _ => exactA Q end]
    | |- kentry_ok _ _ _ (KWord _ 4 _) =>
        eapply L5K.kentry_KWord4; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with D : L5.u32_at _ _ _ _ |- _ => exactA D end]
    | |- kentry_ok _ _ _ (KWord _ 1 _) =>
        eapply L5K.kentry_KWord1; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                  | match goal with B : L5.u8_at _ _ _ _ |- _ => exactA B end]
    end. }
  destruct (PasvD.seg_sound_ax fx E R M SLOTS KNOWN (Forall_nil _))
    as (fx1 & E1 & R1 & M1 & pick & post & PICK & AG & RUN & OUTR & _ & _ & FRAME & CELLS & GROW).
  unfold PasvD.PSS, PasvD.SXALL in PICK. cbn [app map] in PICK.
  exists fx1, R1, M1. split; [exact GROW|].
  split; [intros a; apply FRAME, L5K.outside_nil_e|]. split; [intros i _; apply FRAME, L5K.outside_nil_e|].
  apply L5K.nth_error_single in PICK. subst post.
  split; [exact RUN|].
  split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvD.regs0 PasvD.regs_out0 70 KS_asvD KS_asvD_ok SLOTS AG OUTR x IN)|].
  repeat match goal with |- _ /\ _ => split end.
  all: lazymatch goal with
  | |- getr _ (reg ?i) = _ =>
      rewrite (BG.out_reg PasvD.regs_out0 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
  end.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasvD2 := LibSegBa_asvD2_b.
Definition KS_asvD2 : list nat := Eval vm_compute in (BG.kept_list 70 PasvD2.regs0 PasvD2.regs_out0).
Lemma KS_asvD2_ok : BG.kept_ok 70 PasvD2.regs0 PasvD2.regs_out0 KS_asvD2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma asvD2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 ((((V 37%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 22) = Z_to_bv 64 (V 46%nat) -> getr R (reg 23) = Z_to_bv 64 16384 -> getr R (reg 25) = Z_to_bv 64 (V 39%nat) -> getr R (reg 26) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 36%nat) + 256) -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u64_at RSEGS M (V 37%nat) (V 42%nat) -> 4096 <= (V 42%nat) <= 140737488355328 -> 0 <= (V 46%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb566c M) (st fx' R' 0xb29f8 M')
        /\ (forall x, In x KS_asvD2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 743060
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + (V 46%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 16384).
Proof.
  intros [pos2 fit2] [pos36 fit36] [pos37 fit37] [pos38 fit38] [pos39 fit39] [pos42 fit42] [pos46 fit46] [pos48 fit48] [pos49 fit49] [pos50 fit50]
         [pos51 fit51] [pos52 fit52] [pos53 fit53] [pos54 fit54] [pos55 fit55] [pos56 fit56] [pos57 fit57] [pos58 fit58] [pos59 fit59] [pos60 fit60]
         x2 x8 x9 x18 x19 x20 x21 x22 x23 x25 x26 x27 noimg q_g1309752 d_g1309760 rg2 al2 wr_sl160 q_sl8 q_sl16 q_sl24 q_sl32 q_sl40 q_sl48 q_sl56
         q_sl64 q_sl72 q_sl80 q_sl88 q_sl96 q_sl104 q_sl136 q_sl128 q_sl120 q_sl112 rg36 al36 dsh36 shz36 wr_at36 dsp36 rg37 al37 dsh37 shz37 wr_at37
         dsp37 d36_37 q_at37 rg42 rg46.
  pose (E := Env (fun n => if Nat.eqb n 2 then Z_to_bv 64 (V 2%nat) else reg_ev R (fun k => Z_to_bv 64 (V k)) n) (fun _ => [])).
  pose (VZ := fun j : nat => match j with
    | 2%nat => V 2%nat | 36%nat => V 36%nat | 37%nat => V 37%nat | 38%nat => V 38%nat | 39%nat => V 39%nat | 42%nat => V 42%nat | 46%nat => V 46%nat
    | 48%nat => V 48%nat | 49%nat => V 49%nat | 50%nat => V 50%nat | 51%nat => V 51%nat | 52%nat => V 52%nat | 53%nat => V 53%nat
    | 54%nat => V 54%nat | 55%nat => V 55%nat | 56%nat => V 56%nat | 57%nat => V 57%nat | 58%nat => V 58%nat | 59%nat => V 59%nat
    | 60%nat => V 60%nat | _ => bv_unsigned (ev E j) end).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ j) by BigLinkZA.za_tac VZ 61%nat.
  assert (SLOTS : regs_ok E PasvD2.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. cbn [PasvD2.regs0 tl BG.slots].
    repeat match goal with |- _ /\ _ => split end; [ .. | exact I]; slotP ZA. }
  assert (KNOWN : know_ok RSEGS E M PasvD2.kn0).
  { unfold know_ok, PasvD2.kn0. repeat apply Forall_cons; [ .. | apply Forall_nil].
    all: lazymatch goal with
    | |- kentry_ok _ _ _ (KImg _ _) => apply L5K.kentry_KImg; [lia | lia | exact noimg]
    | |- kentry_ok _ _ _ (KRange _ _ _) => eapply L5K.kentry_KRange; [evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KAlign _ _) =>
        eapply L5K.kentry_KAlign; [evalEk ZA zfacts | lia | match goal with Al : aligned _ _ |- _ => exact Al end]
    | |- kentry_ok _ _ _ (KDisj _ _ _ _) =>
        eapply L5K.kentry_KDisj; [evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KWr _ _) =>
        eapply L5K.kentry_KWr; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                               | match goal with W : L5.writable _ _ _ _ |- _ => exactA W end]
    | |- kentry_ok _ _ _ (KUnk _ _) =>
        eapply L5K.kentry_KUnk; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                | match goal with Df : L5.defined _ _ _ |- _ => exactA Df end]
    | |- kentry_ok _ _ _ (KZero _ _) =>
        eapply L5KA.kentry_KZero; [evalEk ZA zfacts | evalEk ZA zfacts | zfacts; lia | lia | zfacts; lia
                                  | match goal with Z0 : L5KA.zeros_at _ _ _ |- _ => exactA Z0 end]
    | |- kentry_ok _ _ _ (KWord _ 8 _) =>
        eapply L5K.kentry_KWord8; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with Q : L5.u64_at _ _ _ _ |- _ => exactA Q end]
    | |- kentry_ok _ _ _ (KWord _ 4 _) =>
        eapply L5K.kentry_KWord4; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with D : L5.u32_at _ _ _ _ |- _ => exactA D end]
    | |- kentry_ok _ _ _ (KWord _ 1 _) =>
        eapply L5K.kentry_KWord1; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                  | match goal with B : L5.u8_at _ _ _ _ |- _ => exactA B end]
    end. }
  destruct (PasvD2.seg_sound_ax fx E R M SLOTS KNOWN (Forall_nil _))
    as (fx1 & E1 & R1 & M1 & pick & post & PICK & AG & RUN & OUTR & _ & _ & FRAME & CELLS & GROW).
  unfold PasvD2.PSS, PasvD2.SXALL in PICK. cbn [app map] in PICK.
  exists fx1, R1, M1. split; [exact GROW|].
  split; [intros a; apply FRAME, L5K.outside_nil_e|]. split; [intros i _; apply FRAME, L5K.outside_nil_e|].
  apply L5K.nth_error_single in PICK. subst post.
  split; [exact RUN|].
  split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvD2.regs0 PasvD2.regs_out0 70 KS_asvD2 KS_asvD2_ok SLOTS AG OUTR x IN)|].
  repeat match goal with |- _ /\ _ => split end.
  all: lazymatch goal with
  | |- getr _ (reg ?i) = _ =>
      rewrite (BG.out_reg PasvD2.regs_out0 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
  end.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PasvD3 := LibSegBa_asvD3_b.
Definition KS_asvD3_0 : list nat := Eval vm_compute in (BG.kept_list 70 PasvD3.regs0 PasvD3.regs_out0).
Lemma KS_asvD3_0_ok : BG.kept_ok 70 PasvD3.regs0 PasvD3.regs_out0 KS_asvD3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_asvD3_1 : list nat := Eval vm_compute in (BG.kept_list 70 PasvD3.regs0 PasvD3.regs_out1).
Lemma KS_asvD3_1_ok : BG.kept_ok 70 PasvD3.regs0 PasvD3.regs_out1 KS_asvD3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_asvD3_2 : list nat := Eval vm_compute in (BG.kept_list 70 PasvD3.regs0 PasvD3.regs_out2).
Lemma KS_asvD3_2_ok : BG.kept_ok 70 PasvD3.regs0 PasvD3.regs_out2 KS_asvD3_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma asvD3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 10) = Z_to_bv 64 (V 44%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 ((((V 37%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 22) = Z_to_bv 64 (V 46%nat) -> getr R (reg 23) = Z_to_bv 64 16384 -> getr R (reg 25) = Z_to_bv 64 (V 39%nat) -> getr R (reg 26) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 36%nat) + 256) -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 160)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 160) + 160 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 160)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  0 <= (V 44%nat) <= 16384 -> 0 <= (V 46%nat) <= 134217728 -> 1 <= (V 39%nat) <= 18446744073709551615 -> L5.defined M ((V 36%nat) + 256) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5694 M) (st fx' R' 0xb5764 M')
        /\ (forall x, In x KS_asvD3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 743108
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 44%nat) + (V 46%nat))
        /\ getr R' (reg 24) = Z_to_bv 64 (V 44%nat)
        /\ 1 <= (((V 44%nat) - 16384) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb5694 M) (st fx' R' 0xb55a0 M')
        /\ (forall x, In x KS_asvD3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 256)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 39%nat) - (V 44%nat))
        /\ 1 <= (((((V 39%nat) + ((18446744073709551615 * (V 44%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64)
        /\ (((V 44%nat) - 16384) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb5694 M) (st fx' R' 0xb570c M')
        /\ (forall x, In x KS_asvD3_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 38%nat) + (((-1) * (V 39%nat)) + (V 44%nat)))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 256)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 60%nat)
        /\ (((((V 39%nat) + ((18446744073709551615 * (V 44%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ (((V 44%nat) - 16384) mod 2 ^ 64) < 1)).
Proof.
  intros [pos2 fit2] [pos36 fit36] [pos37 fit37] [pos38 fit38] [pos39 fit39] [pos44 fit44] [pos46 fit46] [pos48 fit48] [pos49 fit49] [pos50 fit50]
         [pos51 fit51] [pos52 fit52] [pos53 fit53] [pos54 fit54] [pos55 fit55] [pos56 fit56] [pos57 fit57] [pos58 fit58] [pos59 fit59] [pos60 fit60]
         x2 x8 x9 x10 x18 x19 x20 x21 x22 x23 x25 x26 x27 noimg q_g1309752 d_g1309760 rg2 al2 wr_sl160 q_sl8 q_sl16 q_sl24 q_sl32 q_sl40 q_sl48
         q_sl56 q_sl64 q_sl72 q_sl80 q_sl88 q_sl96 q_sl104 q_sl136 q_sl128 q_sl120 q_sl112 rg36 al36 dsh36 shz36 wr_at36 dsp36 rg37 al37 dsh37 shz37
         wr_at37 dsp37 d36_37 rg44 rg46 rg39 df_at36_256.
  pose (E := Env (fun n => if Nat.eqb n 2 then Z_to_bv 64 (V 2%nat) else reg_ev R (fun k => Z_to_bv 64 (V k)) n) (fun _ => [])).
  pose (VZ := fun j : nat => match j with
    | 2%nat => V 2%nat | 36%nat => V 36%nat | 37%nat => V 37%nat | 38%nat => V 38%nat | 39%nat => V 39%nat | 44%nat => V 44%nat | 46%nat => V 46%nat
    | 48%nat => V 48%nat | 49%nat => V 49%nat | 50%nat => V 50%nat | 51%nat => V 51%nat | 52%nat => V 52%nat | 53%nat => V 53%nat
    | 54%nat => V 54%nat | 55%nat => V 55%nat | 56%nat => V 56%nat | 57%nat => V 57%nat | 58%nat => V 58%nat | 59%nat => V 59%nat
    | 60%nat => V 60%nat | _ => bv_unsigned (ev E j) end).
  assert (ZA : forall j, bv_unsigned (ev E j) = VZ j) by BigLinkZA.za_tac VZ 61%nat.
  assert (SLOTS : regs_ok E PasvD3.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. cbn [PasvD3.regs0 tl BG.slots].
    repeat match goal with |- _ /\ _ => split end; [ .. | exact I]; slotP ZA. }
  assert (KNOWN : know_ok RSEGS E M PasvD3.kn0).
  { unfold know_ok, PasvD3.kn0. repeat apply Forall_cons; [ .. | apply Forall_nil].
    all: lazymatch goal with
    | |- kentry_ok _ _ _ (KImg _ _) => apply L5K.kentry_KImg; [lia | lia | exact noimg]
    | |- kentry_ok _ _ _ (KRange _ _ _) => eapply L5K.kentry_KRange; [evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KAlign _ _) =>
        eapply L5K.kentry_KAlign; [evalEk ZA zfacts | lia | match goal with Al : aligned _ _ |- _ => exact Al end]
    | |- kentry_ok _ _ _ (KDisj _ _ _ _) =>
        eapply L5K.kentry_KDisj; [evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | evalEk ZA zfacts | lia]
    | |- kentry_ok _ _ _ (KWr _ _) =>
        eapply L5K.kentry_KWr; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                               | match goal with W : L5.writable _ _ _ _ |- _ => exactA W end]
    | |- kentry_ok _ _ _ (KUnk _ _) =>
        eapply L5K.kentry_KUnk; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                | match goal with Df : L5.defined _ _ _ |- _ => exactA Df end]
    | |- kentry_ok _ _ _ (KZero _ _) =>
        eapply L5KA.kentry_KZero; [evalEk ZA zfacts | evalEk ZA zfacts | zfacts; lia | lia | zfacts; lia
                                  | match goal with Z0 : L5KA.zeros_at _ _ _ |- _ => exactA Z0 end]
    | |- kentry_ok _ _ _ (KWord _ 8 _) =>
        eapply L5K.kentry_KWord8; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with Q : L5.u64_at _ _ _ _ |- _ => exactA Q end]
    | |- kentry_ok _ _ _ (KWord _ 4 _) =>
        eapply L5K.kentry_KWord4; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia
                                  | match goal with D : L5.u32_at _ _ _ _ |- _ => exactA D end]
    | |- kentry_ok _ _ _ (KWord _ 1 _) =>
        eapply L5K.kentry_KWord1; [evalEk ZA zfacts | evalEk ZA zfacts | lia | lia | lia
                                  | match goal with B : L5.u8_at _ _ _ _ |- _ => exactA B end]
    end. }
  destruct (PasvD3.seg_sound_ax fx E R M SLOTS KNOWN (Forall_nil _))
    as (fx1 & E1 & R1 & M1 & pick & post & PICK & AG & RUN & OUTR & _ & _ & FRAME & CELLS & GROW).
  unfold PasvD3.PSS, PasvD3.SXALL in PICK. cbn [app map] in PICK.
  exists fx1, R1, M1. split; [exact GROW|].
  split; [intros a OUT; apply FRAME; eapply L5K.outside_cons_e; [evalEk' ZA AG zfacts | evalEk' ZA AG zfacts | lia | apply L5K.outside_nil_e]|].
  split; [intros i Ri OUT; apply FRAME; eapply L5K.outside_cons_e; [evalEk' ZA AG zfacts | evalEk' ZA AG zfacts | rewrite BG.unsigned_lit by lia; lia | apply L5K.outside_nil_e]|].
  destruct pick as [|[|[|pick]]]; cbn [nth_error] in PICK; [ .. | destruct pick; cbn in PICK; discriminate];
    injection PICK as PICK; subst post.
  - left. split; [exact RUN|].
    split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvD3.regs0 PasvD3.regs_out0 70 KS_asvD3_0 KS_asvD3_0_ok SLOTS AG OUTR x IN)|].
    assert (CK : Forall (kentry_ok RSEGS E1 M1) PasvD3.cells0) by (apply Forall_forall; exact CELLS).
    unfold PasvD3.cells0 in CK.
    repeat (apply Forall_cons_iff in CK; let c := fresh "cell" in destruct CK as [c CK]).
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- getr _ (reg ?i) = _ =>
        rewrite (BG.out_reg PasvD3.regs_out0 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
    | |- ?c <= ?T =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    end.
  - right; left. split; [exact RUN|].
    split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvD3.regs0 PasvD3.regs_out1 70 KS_asvD3_1 KS_asvD3_1_ok SLOTS AG OUTR x IN)|].
    assert (CK : Forall (kentry_ok RSEGS E1 M1) PasvD3.cells1) by (apply Forall_forall; exact CELLS).
    unfold PasvD3.cells1 in CK.
    repeat (apply Forall_cons_iff in CK; let c := fresh "cell" in destruct CK as [c CK]).
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- getr _ (reg ?i) = _ =>
        rewrite (BG.out_reg PasvD3.regs_out1 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
    | |- ?T < ?c =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    | |- ?c <= ?T =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    end.
  - right; right. split; [exact RUN|].
    split; [intros x IN; exact (BG.kept_regs E E1 R R1 PasvD3.regs0 PasvD3.regs_out2 70 KS_asvD3_2 KS_asvD3_2_ok SLOTS AG OUTR x IN)|].
    assert (CK : Forall (kentry_ok RSEGS E1 M1) PasvD3.cells2) by (apply Forall_forall; exact CELLS).
    unfold PasvD3.cells2 in CK.
    repeat (apply Forall_cons_iff in CK; let c := fresh "cell" in destruct CK as [c CK]).
    repeat match goal with |- _ /\ _ => split end.
    all: lazymatch goal with
    | |- getr _ (reg ?i) = _ =>
        rewrite (BG.out_reg PasvD3.regs_out2 E1 R1 i OUTR) by lia; L5K.norm_expr; first [reflexivity | wordP' ZA AG]
    | |- ?T < ?c =>
        match goal with C : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU ?x ?y) _ _) |- _ =>
          assert (SV : bv_unsigned (edenot E1 (EAlu ALU_SLTU x y)) = if T <? c then 1 else 0)
            by (eapply BG.zeval_kept; [exact AG | reflexivity
                | rewrite (BL.zeval_agree 70 (BL.uv E) VZ); [reflexivity | intros n _; exact (ZA n) | reflexivity]]);
          cbn [kentry_ok] in C; rewrite SV in C; revert C; destruct (Z.ltb_spec T c); intros C; cbv beta iota in C; lia
        end
    end.
Qed.
(* [comment removed for export] *)

End PMASRVP.
