(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigLinkZA.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Bo0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA XIcptAB0 XIcptAs0KitB0.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegY_ue3t2_v1.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5BE3P5.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)).

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
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | solve_modk k ].
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
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
(* [comment removed for export] *)
Module Pue3t2_v1 := LibSegY_ue3t2_v1.
Definition KS_ue3t2_v1 : list nat := Eval vm_compute in (BG.kept_list 103 Pue3t2_v1.regs0 Pue3t2_v1.regs_out0).
Lemma KS_ue3t2_v1_ok : BG.kept_ok 103 Pue3t2_v1.regs0 Pue3t2_v1.regs_out0 KS_ue3t2_v1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ue3t2_v1_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 32%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 -> 0 <= (V 80%nat) < 2 ^ 64 -> 0 <= (V 81%nat) < 2 ^ 64 -> 0 <= (V 82%nat) < 2 ^ 64 -> 0 <= (V 83%nat) < 2 ^ 64 -> 0 <= (V 84%nat) < 2 ^ 64 -> 0 <= (V 85%nat) < 2 ^ 64 -> 0 <= (V 86%nat) < 2 ^ 64 -> 0 <= (V 87%nat) < 2 ^ 64 -> 0 <= (V 88%nat) < 2 ^ 64 -> 0 <= (V 89%nat) < 2 ^ 64 -> 0 <= (V 90%nat) < 2 ^ 64 -> 0 <= (V 91%nat) < 2 ^ 64 -> 0 <= (V 92%nat) < 2 ^ 64 -> 0 <= (V 93%nat) < 2 ^ 64 -> 0 <= (V 94%nat) < 2 ^ 64 -> 0 <= (V 95%nat) < 2 ^ 64 -> 0 <= (V 96%nat) < 2 ^ 64 -> 0 <= (V 97%nat) < 2 ^ 64 -> 0 <= (V 98%nat) < 2 ^ 64 -> 0 <= (V 99%nat) < 2 ^ 64 -> 0 <= (V 100%nat) < 2 ^ 64 -> 0 <= (V 101%nat) < 2 ^ 64 -> 0 <= (V 102%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 3) = Z_to_bv 64 67584 -> getr R (reg 4) = Z_to_bv 64 6363400 -> getr R (reg 8) = Z_to_bv 64 ((V 10%nat) - 32) -> getr R (reg 9) = Z_to_bv 64 884616 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 10608) 10544 -> L5.defined M ((V 2%nat) - 10608) 10544 ->
  4224 <= (V 10%nat) <= 140737479966720 -> aligned (V 10%nat) 16 -> L5.writable RSEGS M ((V 10%nat) - 128) 144 -> L5.defined M ((V 10%nat) - 128) 144 ->
  (2147446784 + 17592186048512 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 144 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450864) 18 -> 1099511627776 <= (V 32%nat) <= 140737488355328 -> aligned (V 32%nat) 8 ->
  (((V 2%nat) - 10608) + 14640 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 144 <= ((V 2%nat) - 10608)) -> (((V 10%nat) - 128) + 144 <= (V 32%nat) \/ (V 32%nat) + 160 <= ((V 10%nat) - 128)) -> (((V 10%nat) - 128) + 144 <= (V 41%nat) \/ (V 41%nat) + 160 <= ((V 10%nat) - 128)) -> (((V 10%nat) - 128) + 144 <= (V 42%nat) \/ (V 42%nat) + 64 <= ((V 10%nat) - 128)) ->
  (((V 10%nat) - 128) + 144 <= (V 43%nat) \/ (V 43%nat) + 4096 <= ((V 10%nat) - 128)) -> (((V 2%nat) - 10608) + 11920 <= (V 32%nat) \/ (V 32%nat) + 160 <= ((V 2%nat) - 10608)) -> ((V 32%nat) + 160 <= (V 41%nat) \/ (V 41%nat) + 160 <= (V 32%nat)) -> ((V 32%nat) + 160 <= (V 42%nat) \/ (V 42%nat) + 64 <= (V 32%nat)) ->
  ((V 32%nat) + 160 <= (V 43%nat) \/ (V 43%nat) + 4096 <= (V 32%nat)) -> (((V 2%nat) - 10608) + 14640 <= (V 41%nat) \/ (V 41%nat) + 160 <= ((V 2%nat) - 10608)) -> ((V 41%nat) + 160 <= (V 42%nat) \/ (V 42%nat) + 64 <= (V 41%nat)) -> ((V 41%nat) + 160 <= (V 43%nat) \/ (V 43%nat) + 4096 <= (V 41%nat)) ->
  (((V 2%nat) - 10608) + 14640 <= (V 42%nat) \/ (V 42%nat) + 64 <= ((V 2%nat) - 10608)) -> ((V 42%nat) + 64 <= (V 43%nat) \/ (V 43%nat) + 4096 <= (V 42%nat)) -> (((V 2%nat) - 10608) + 14640 <= (V 43%nat) \/ (V 43%nat) + 4096 <= ((V 2%nat) - 10608)) -> (((V 10%nat) - 128) + 144 <= 65536 \/ 65536 + 6438912 <= ((V 10%nat) - 128)) ->
  ((V 41%nat) + 160 <= 65536 \/ 65536 + 6438912 <= (V 41%nat)) -> ((V 42%nat) + 64 <= 65536 \/ 65536 + 6438912 <= (V 42%nat)) -> ((V 43%nat) + 4096 <= 65536 \/ 65536 + 6438912 <= (V 43%nat)) -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147449554) 1318 ->
  L5.img_clear M 65536 884736 -> L5.img_clear M 895824 895856 -> L5.u64_at RSEGS M 877768 911160 -> L5.u64_at RSEGS M 911160 2147450880 ->
  L5.u64_at RSEGS M 877776 914472 -> L5.u64_at RSEGS M 914472 0 -> L5.u64_at RSEGS M 877784 914480 -> L5.u64_at RSEGS M 914480 0 ->
  L5.u64_at RSEGS M 877792 914464 -> L5.u64_at RSEGS M 914464 140737488355327 -> L5.u64_at RSEGS M 880688 914457 -> L5.u8_at RSEGS M 914457 1 ->
  L5.u64_at RSEGS M 885800 837440 -> L5.u64_at RSEGS M 885792 836412 -> L5.u8_at RSEGS M 914456 1 -> L5.u64_at RSEGS M 885576 839856 ->
  L5.u64_at RSEGS M 6363392 6363432 -> L5.u64_at RSEGS M 6363440 6365448 -> L5.u8_at RSEGS M 909216 1 -> L5.u32_at RSEGS M 909220 0 ->
  L5.u64_at RSEGS M 6363312 6499504 -> L5.u64_at RSEGS M 877752 1507944 -> L5.u8_at RSEGS M 1508081 1 -> L5.u64_at RSEGS M 877848 1499608 ->
  L5.u32_at RSEGS M 1499608 0 -> L5.u64_at RSEGS M 881296 8 -> L5.u64_at RSEGS M 6499504 (V 41%nat) -> L5.u64_at RSEGS M ((V 41%nat) + 152) (V 42%nat) ->
  L5.u64_at RSEGS M ((V 42%nat) + 48) (V 44%nat) -> L5.u64_at RSEGS M ((V 42%nat) + 56) (V 45%nat) -> L5.u64_at RSEGS M 6363408 (V 43%nat) -> L5.u64_at RSEGS M ((V 43%nat) + 24) 6363400 ->
  4096 <= (V 41%nat) <= 140737479966560 -> 4096 <= (V 42%nat) <= 140737479966656 -> 4096 <= (V 43%nat) <= 140737479962624 -> L5.u64_at RSEGS M 885704 746772 ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) 725808 -> L5.u64_at RSEGS M ((V 2%nat) - 48) ((V 10%nat) - 128) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 46%nat) -> L5.u64_at RSEGS M 6494536 (V 33%nat) ->
  L5.u64_at RSEGS M 6495136 (V 32%nat) -> L5.u64_at RSEGS M (V 32%nat) 3 -> L5.u64_at RSEGS M ((V 32%nat) + 8) 65600 -> L5.u64_at RSEGS M ((V 32%nat) + 16) 4 ->
  L5.u64_at RSEGS M ((V 32%nat) + 24) 56 -> L5.u64_at RSEGS M ((V 32%nat) + 32) 5 -> L5.u64_at RSEGS M ((V 32%nat) + 40) 11 -> L5.u64_at RSEGS M ((V 32%nat) + 48) 16 ->
  L5.u64_at RSEGS M ((V 32%nat) + 56) (V 39%nat) -> L5.u64_at RSEGS M ((V 32%nat) + 64) 6 -> L5.u64_at RSEGS M ((V 32%nat) + 72) 4096 -> L5.u64_at RSEGS M ((V 32%nat) + 80) 11 ->
  L5.u64_at RSEGS M ((V 32%nat) + 88) (V 34%nat) -> L5.u64_at RSEGS M ((V 32%nat) + 96) 12 -> L5.u64_at RSEGS M ((V 32%nat) + 104) (V 34%nat) -> L5.u64_at RSEGS M ((V 32%nat) + 112) 23 ->
  L5.u64_at RSEGS M ((V 32%nat) + 120) 0 -> L5.u64_at RSEGS M ((V 32%nat) + 128) 25 -> L5.u64_at RSEGS M ((V 32%nat) + 136) (V 36%nat) -> L5.u64_at RSEGS M ((V 32%nat) + 144) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) 591944 -> L5.u64_at RSEGS M ((V 2%nat) - 16) ((V 2%nat) + 128) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 2%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) - 32) 4849336966747728640 -> L5.u64_at RSEGS M ((V 2%nat) + 120) 589268 -> L5.u64_at RSEGS M ((V 2%nat) + 112) ((V 2%nat) + 256) -> L5.u64_at RSEGS M ((V 2%nat) + 104) ((V 2%nat) + 128) ->
  L5.u64_at RSEGS M ((V 2%nat) + 96) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 88) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 80) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 72) (V 51%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 64) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 56) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 48) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 40) (V 55%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 32) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 248) 602428 -> L5.u64_at RSEGS M ((V 2%nat) + 240) ((V 2%nat) + 640) -> L5.u64_at RSEGS M ((V 2%nat) + 232) ((V 2%nat) + 256) ->
  L5.u64_at RSEGS M ((V 2%nat) + 224) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 216) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 208) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 200) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 192) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 184) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 176) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 168) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 160) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 632) 609336 -> L5.u64_at RSEGS M ((V 2%nat) + 624) ((V 2%nat) + 736) -> L5.u64_at RSEGS M ((V 2%nat) + 616) ((V 2%nat) + 640) ->
  L5.u64_at RSEGS M ((V 2%nat) + 608) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 600) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 592) ((V 2%nat) + 744) -> L5.u64_at RSEGS M ((V 2%nat) + 584) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 576) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 568) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 560) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 552) (V 72%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 544) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 536) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 728) 607300 -> L5.u64_at RSEGS M ((V 2%nat) + 720) (V 75%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 712) (V 76%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 704) (V 77%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 696) (V 78%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 688) (V 79%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 680) (V 80%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 672) (V 81%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 664) (V 82%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 656) (V 83%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 792) 603324 -> L5.u64_at RSEGS M ((V 2%nat) + 784) ((V 2%nat) + 1184) -> L5.u64_at RSEGS M ((V 2%nat) + 776) ((V 2%nat) + 800) -> L5.u64_at RSEGS M ((V 2%nat) + 1176) 600132 ->
  L5.u64_at RSEGS M ((V 2%nat) + 1168) ((V 2%nat) + 1296) -> L5.u64_at RSEGS M ((V 2%nat) + 1160) ((V 2%nat) + 1184) -> L5.u64_at RSEGS M ((V 2%nat) + 1152) (V 84%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 1144) (V 85%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 1136) (V 86%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 1128) (V 87%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 1120) (V 88%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 1112) (V 89%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 1104) (V 90%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 1096) (V 91%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 1088) (V 92%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 1080) (V 93%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 1288) 584500 -> L5.u64_at RSEGS M ((V 2%nat) + 1280) (V 94%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 1272) ((V 2%nat) + 1312) -> L5.u64_at RSEGS M ((V 2%nat) + 1264) (V 95%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 1256) (V 96%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 1248) (V 97%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 1240) (V 98%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 1232) (V 99%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 1224) (V 100%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 1216) (V 101%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 1304) 582404 -> L5.u64_at RSEGS M ((V 2%nat) + 1296) (V 102%nat) ->
  L5.u64_at RSEGS M ((V 10%nat) - 112) 864552 -> L5.u8_at RSEGS M 6363185 1 -> L5.u8_at RSEGS M 6363186 0 -> L5.u8_at RSEGS M 6363187 1 ->
  L5.u8_at RSEGS M 6363188 0 -> L5.u8_at RSEGS M 6363189 1 -> L5.u8_at RSEGS M 6363190 0 -> L5.writable RSEGS M 6363185 6 ->
  L5.writable RSEGS M ((V 2%nat) - 64) 8 -> L5.writable RSEGS M ((V 2%nat) - 56) 8 -> L5.writable RSEGS M ((V 2%nat) - 48) 8 -> L5.writable RSEGS M ((V 2%nat) - 40) 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 10608) <= bv_unsigned a < ((V 2%nat) - 10608) + 10544) -> ~ (((V 10%nat) - 68) <= bv_unsigned a < ((V 10%nat) - 68) + 68) -> ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 8) -> ~ (((V 2%nat) - 56) <= bv_unsigned a < ((V 2%nat) - 56) + 8) -> ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 8) -> ~ (((V 2%nat) - 40) <= bv_unsigned a < ((V 2%nat) - 40) + 8) -> ~ (6363185 <= bv_unsigned a < 6363185 + 6) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 10608) <= i < ((V 2%nat) - 10608) + 10544) -> ~ (((V 10%nat) - 68) <= i < ((V 10%nat) - 68) + 68) -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 8) -> ~ (((V 2%nat) - 56) <= i < ((V 2%nat) - 56) + 8) -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 8) -> ~ (((V 2%nat) - 40) <= i < ((V 2%nat) - 40) + 8) -> ~ (6363185 <= i < 6363185 + 6) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x53f9c M) (st fx' R' 0x9087c M')
        /\ (forall x, In x KS_ue3t2_v1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 591996
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 6) = Z_to_bv 64 746772
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) + 128)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 10%nat) - 32)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) - 8) ((V 2%nat) + 1312)
        /\ L5.u64_at RSEGS M' ((V 10%nat) - 40) (V 10%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) - 48) 583040
        /\ L5.u64_at RSEGS M' ((V 10%nat) - 56) 157360
        /\ L5.u64_at RSEGS M' ((V 10%nat) - 64) 157499
        /\ L5.u32_at RSEGS M' ((V 10%nat) - 68) 1
        /\ L5.u64_at RSEGS M' ((V 10%nat) - 16) 0
        /\ L5.defined M' ((V 10%nat) - 128) 60
        /\ L5.defined M' ((V 10%nat) - 32) 16
        /\ L5.defined M' (V 10%nat) 16
        /\ L5.u64_at RSEGS M' ((V 10%nat) - 32) 4849336966747728640
        /\ L5.u8_at RSEGS M' 6363185 1
        /\ L5.u8_at RSEGS M' 6363186 0
        /\ L5.u8_at RSEGS M' 6363187 1
        /\ L5.u8_at RSEGS M' 6363188 0
        /\ L5.u8_at RSEGS M' 6363189 1
        /\ L5.u8_at RSEGS M' 6363190 0).
Proof.
  intros [HV2l HV2r] [HV10l HV10r] [HV32l HV32r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV39l HV39r] [HV40l HV40r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] [HV52l HV52r] [HV53l HV53r] [HV54l HV54r] [HV55l HV55r] [HV56l HV56r] [HV57l HV57r] [HV58l HV58r] [HV59l HV59r] [HV60l HV60r] [HV61l HV61r] [HV62l HV62r] [HV63l HV63r] [HV64l HV64r] [HV65l HV65r] [HV66l HV66r] [HV67l HV67r] [HV68l HV68r] [HV69l HV69r] [HV70l HV70r] [HV71l HV71r] [HV72l HV72r] [HV73l HV73r] [HV74l HV74r] [HV75l HV75r] [HV76l HV76r] [HV77l HV77r] [HV78l HV78r] [HV79l HV79r] [HV80l HV80r] [HV81l HV81r] [HV82l HV82r] [HV83l HV83r] [HV84l HV84r] [HV85l HV85r] [HV86l HV86r] [HV87l HV87r] [HV88l HV88r] [HV89l HV89r] [HV90l HV90r] [HV91l HV91r] [HV92l HV92r] [HV93l HV93r] [HV94l HV94r] [HV95l HV95r] [HV96l HV96r] [HV97l HV97r] [HV98l HV98r] [HV99l HV99r] [HV100l HV100r] [HV101l HV101r] [HV102l HV102r] G2 G3 G4 G8 G9 G10 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 K8 K9 [K10l K10r] K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 [K64l K64r] [K65l K65r] [K66l K66r] K67 K68 K69 K70 K71 K72 K73 K74 K75 K76 K77 K78 K79 K80 K81 K82 K83 K84 K85 K86 K87 K88 K89 K90 K91 K92 K93 K94 K95 K96 K97 K98 K99 K100 K101 K102 K103 K104 K105 K106 K107 K108 K109 K110 K111 K112 K113 K114 K115 K116 K117 K118 K119 K120 K121 K122 K123 K124 K125 K126 K127 K128 K129 K130 K131 K132 K133 K134 K135 K136 K137 K138 K139 K140 K141 K142 K143 K144 K145 K146 K147 K148 K149 K150 K151 K152 K153 K154 K155 K156 K157 K158 K159 K160 K161 K162 K163 K164 K165 K166 K167 K168 K169 K170 K171 K172 K173 K174 K175 K176 K177 K178 K179 K180 K181 K182 K183.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 10%nat => Z_to_bv 64 (V 10%nat) | 32%nat => Z_to_bv 64 (V 32%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | 55%nat => Z_to_bv 64 (V 55%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 78%nat => Z_to_bv 64 (V 78%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | 80%nat => Z_to_bv 64 (V 80%nat) | 81%nat => Z_to_bv 64 (V 81%nat) | 82%nat => Z_to_bv 64 (V 82%nat) | 83%nat => Z_to_bv 64 (V 83%nat) | 84%nat => Z_to_bv 64 (V 84%nat) | 85%nat => Z_to_bv 64 (V 85%nat) | 86%nat => Z_to_bv 64 (V 86%nat) | 87%nat => Z_to_bv 64 (V 87%nat) | 88%nat => Z_to_bv 64 (V 88%nat) | 89%nat => Z_to_bv 64 (V 89%nat) | 90%nat => Z_to_bv 64 (V 90%nat) | 91%nat => Z_to_bv 64 (V 91%nat) | 92%nat => Z_to_bv 64 (V 92%nat) | 93%nat => Z_to_bv 64 (V 93%nat) | 94%nat => Z_to_bv 64 (V 94%nat) | 95%nat => Z_to_bv 64 (V 95%nat) | 96%nat => Z_to_bv 64 (V 96%nat) | 97%nat => Z_to_bv 64 (V 97%nat) | 98%nat => Z_to_bv 64 (V 98%nat) | 99%nat => Z_to_bv 64 (V 99%nat) | 100%nat => Z_to_bv 64 (V 100%nat) | 101%nat => Z_to_bv 64 (V 101%nat) | 102%nat => Z_to_bv 64 (V 102%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 10%nat => (V 10%nat) | 32%nat => (V 32%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | 54%nat => (V 54%nat) | 55%nat => (V 55%nat) | 56%nat => (V 56%nat) | 57%nat => (V 57%nat) | 58%nat => (V 58%nat) | 59%nat => (V 59%nat) | 60%nat => (V 60%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 63%nat => (V 63%nat) | 64%nat => (V 64%nat) | 65%nat => (V 65%nat) | 66%nat => (V 66%nat) | 67%nat => (V 67%nat) | 68%nat => (V 68%nat) | 69%nat => (V 69%nat) | 70%nat => (V 70%nat) | 71%nat => (V 71%nat) | 72%nat => (V 72%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | 75%nat => (V 75%nat) | 76%nat => (V 76%nat) | 77%nat => (V 77%nat) | 78%nat => (V 78%nat) | 79%nat => (V 79%nat) | 80%nat => (V 80%nat) | 81%nat => (V 81%nat) | 82%nat => (V 82%nat) | 83%nat => (V 83%nat) | 84%nat => (V 84%nat) | 85%nat => (V 85%nat) | 86%nat => (V 86%nat) | 87%nat => (V 87%nat) | 88%nat => (V 88%nat) | 89%nat => (V 89%nat) | 90%nat => (V 90%nat) | 91%nat => (V 91%nat) | 92%nat => (V 92%nat) | 93%nat => (V 93%nat) | 94%nat => (V 94%nat) | 95%nat => (V 95%nat) | 96%nat => (V 96%nat) | 97%nat => (V 97%nat) | 98%nat => (V 98%nat) | 99%nat => (V 99%nat) | 100%nat => (V 100%nat) | 101%nat => (V 101%nat) | 102%nat => (V 102%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 103%nat. }
  assert (HR: regs_ok E Pue3t2_v1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pue3t2_v1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pue3t2_v1.kn0).
  { unfold know_ok, Pue3t2_v1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14 K18 K21 K22 K23 K28 K64l K64r) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV43l HV43r K16 K20 K23 K25 K26 K30 K66l K66r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14 K18 K21 K22 K23 K28 K64l K64r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV43l HV43r K16 K20 K23 K25 K26 K30 K66l K66r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14 K18 K21 K22 K23 K28 K64l K64r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K14 K18 K21 K22 K23 K28 K64l K64r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K14 K18 K21 K22 K23 K28 K64l K64r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV43l HV43r K16 K20 K23 K25 K26 K30 K66l K66r) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV43l HV43r K16 K20 K23 K25 K26 K30 K66l K66r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV43l HV43r K16 K20 K23 K25 K26 K30 K66l K66r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K14 K18 K21 K22 K23 K28 K64l K64r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV43l HV43r K16 K20 K23 K25 K26 K30 K66l K66r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K14 K18 K21 K22 K23 K28 K64l K64r) | clear; lia | clear; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV41l HV41r K14 K18 K21 K22 K23 K28 K64l K64r) | evalEk ZA ltac:(clear - HV42l HV42r K15 K19 K22 K24 K25 K29 K65l K65r) | clear - HV41l HV41r K14 K18 K21 K22 K23 K28 K64l K64r; lia | clear - HV41l HV41r K14 K18 K21 K22 K23 K28 K64l K64r; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV42l HV42r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV42l HV42r K15 K19 K22 K24 K25 K29 K65l K65r; lia | clear - HV42l HV42r K15 K19 K22 K24 K25 K29 K65l K65r; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV42l HV42r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV42l HV42r K15 K19 K22 K24 K25 K29 K65l K65r; lia | clear - HV42l HV42r K15 K19 K22 K24 K25 K29 K65l K65r; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV43l HV43r K16 K20 K23 K25 K26 K30 K66l K66r) | clear; lia | clear; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV43l HV43r K16 K20 K23 K25 K26 K30 K66l K66r) | evalEk ZA ltac:(clear) | clear - HV43l HV43r K16 K20 K23 K25 K26 K30 K66l K66r; lia | clear - HV43l HV43r K16 K20 K23 K25 K26 K30 K66l K66r; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14 K18 K21 K22 K23 K28 K64l K64r) | exact (conj K64l K64r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K15 K19 K22 K24 K25 K29 K65l K65r) | exact (conj K65l K65r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K16 K20 K23 K25 K26 K30 K66l K66r) | exact (conj K66l K66r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K70]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r) | clear; lia | clear; lia | exactA K71]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | clear; lia | clear; lia | exactA K72]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K73]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K74]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K75]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K76]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K77]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K78]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K79]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K80]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K81]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K82]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K83]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K84]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K85]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K86]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K87]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K88]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K89]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K90]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K91]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K92]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K93]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K94]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K95]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | exactA K96]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K97]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K98]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K99]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K100]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K101]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K102]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K103]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K104]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K105]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K106]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K107]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K108]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K109]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K110]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K111]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K112]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K113]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K114]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K115]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K116]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K117]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K118]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K119]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K120]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K121]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K122]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K123]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K124]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K125]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K126]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K127]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K128]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K129]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K130]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K131]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K132]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K133]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K134]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K135]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV76l HV76r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K136]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV77l HV77r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K137]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV78l HV78r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K138]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV79l HV79r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K139]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV80l HV80r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K140]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV81l HV81r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K141]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV82l HV82r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K142]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV83l HV83r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K143]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K144]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K145]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K146]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K147]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K148]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K149]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV84l HV84r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K150]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV85l HV85r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K151]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV86l HV86r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K152]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV87l HV87r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K153]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV88l HV88r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K154]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV89l HV89r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K155]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV90l HV90r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K156]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV91l HV91r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K157]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV92l HV92r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K158]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV93l HV93r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K159]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K160]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV94l HV94r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K161]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K162]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV95l HV95r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K163]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV96l HV96r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K164]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV97l HV97r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K165]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV98l HV98r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K166]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV99l HV99r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K167]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV100l HV100r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K168]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV101l HV101r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K169]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K170]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV102l HV102r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K171]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | exactA K172]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K173]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K174]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K175]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K176]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K177]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K178]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K179]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K180]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K181]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K182]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K183]. }
    apply Forall_nil. }
  destruct (Pue3t2_v1.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pue3t2_v1.NX0 with 103%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 10608) <= bv_unsigned a < ((V 2%nat) - 10608) + 10544) -> ~ (((V 10%nat) - 68) <= bv_unsigned a < ((V 10%nat) - 68) + 68) -> ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 8) -> ~ (((V 2%nat) - 56) <= bv_unsigned a < ((V 2%nat) - 56) + 8) -> ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 8) -> ~ (((V 2%nat) - 40) <= bv_unsigned a < ((V 2%nat) - 40) + 8) -> ~ (6363185 <= bv_unsigned a < 6363185 + 6) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply Hfr. unfold Pue3t2_v1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26 Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26 Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn6; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pue3t2_v1.ps0) with 0x9087c in Hms. change (SR.ps_regs Pue3t2_v1.ps0) with (map (fun i => (i, nth i Pue3t2_v1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pue3t2_v1.ps0) with Pue3t2_v1.cells0 in Hcells. unfold Pue3t2_v1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pue3t2_v1.regs0 Pue3t2_v1.regs_out0 103 KS_ue3t2_v1 KS_ue3t2_v1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pue3t2_v1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pue3t2_v1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3t2_v1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pue3t2_v1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3t2_v1.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth Pue3t2_v1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3t2_v1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pue3t2_v1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3t2_v1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pue3t2_v1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3t2_v1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pue3t2_v1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3t2_v1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pue3t2_v1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3t2_v1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pue3t2_v1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End L5BE3P5.
