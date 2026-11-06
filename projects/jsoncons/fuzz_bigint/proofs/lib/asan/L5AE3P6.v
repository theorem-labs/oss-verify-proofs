(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigLinkZA.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan As0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA XIcptA XIcptAs0Kit.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegZ_ue3r1.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5AE3P6.
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)).

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
Module Pue3r1 := LibSegZ_ue3r1.
Definition KS_ue3r1 : list nat := Eval vm_compute in (BG.kept_list 63 Pue3r1.regs0 Pue3r1.regs_out0).
Lemma KS_ue3r1_ok : BG.kept_ok 63 Pue3r1.regs0 Pue3r1.regs_out0 KS_ue3r1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ue3r1_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 32%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 3) = Z_to_bv 64 67584 -> getr R (reg 4) = Z_to_bv 64 6360328 -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) + 128) -> getr R (reg 10) = Z_to_bv 64 ((V 10%nat) - 32) ->
  140735332552704 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 10560) 10560 -> L5.defined M ((V 2%nat) - 10560) 10560 ->
  4224 <= (V 10%nat) <= 140737479966720 -> aligned (V 10%nat) 16 -> L5.writable RSEGS M ((V 10%nat) - 128) 144 -> L5.defined M ((V 10%nat) - 128) 144 ->
  (2147446784 + 17592186048512 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 144 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450864) 18 -> 1099511627776 <= (V 32%nat) <= 140737488355328 -> aligned (V 32%nat) 8 ->
  (((V 2%nat) - 10560) + 14656 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 144 <= ((V 2%nat) - 10560)) -> (((V 10%nat) - 128) + 144 <= (V 32%nat) \/ (V 32%nat) + 160 <= ((V 10%nat) - 128)) -> (((V 10%nat) - 128) + 144 <= (V 40%nat) \/ (V 40%nat) + 160 <= ((V 10%nat) - 128)) -> (((V 10%nat) - 128) + 144 <= (V 41%nat) \/ (V 41%nat) + 64 <= ((V 10%nat) - 128)) ->
  (((V 10%nat) - 128) + 144 <= (V 42%nat) \/ (V 42%nat) + 4096 <= ((V 10%nat) - 128)) -> (((V 2%nat) - 10560) + 11776 <= (V 32%nat) \/ (V 32%nat) + 160 <= ((V 2%nat) - 10560)) -> ((V 32%nat) + 160 <= (V 40%nat) \/ (V 40%nat) + 160 <= (V 32%nat)) -> ((V 32%nat) + 160 <= (V 41%nat) \/ (V 41%nat) + 64 <= (V 32%nat)) ->
  ((V 32%nat) + 160 <= (V 42%nat) \/ (V 42%nat) + 4096 <= (V 32%nat)) -> (((V 2%nat) - 10560) + 14656 <= (V 40%nat) \/ (V 40%nat) + 160 <= ((V 2%nat) - 10560)) -> ((V 40%nat) + 160 <= (V 41%nat) \/ (V 41%nat) + 64 <= (V 40%nat)) -> ((V 40%nat) + 160 <= (V 42%nat) \/ (V 42%nat) + 4096 <= (V 40%nat)) ->
  (((V 2%nat) - 10560) + 14656 <= (V 41%nat) \/ (V 41%nat) + 64 <= ((V 2%nat) - 10560)) -> ((V 41%nat) + 64 <= (V 42%nat) \/ (V 42%nat) + 4096 <= (V 41%nat)) -> (((V 2%nat) - 10560) + 14656 <= (V 42%nat) \/ (V 42%nat) + 4096 <= ((V 2%nat) - 10560)) -> (((V 10%nat) - 128) + 144 <= 65536 \/ 65536 + 6434816 <= ((V 10%nat) - 128)) ->
  ((V 40%nat) + 160 <= 65536 \/ 65536 + 6434816 <= (V 40%nat)) -> ((V 41%nat) + 64 <= 65536 \/ 65536 + 6434816 <= (V 41%nat)) -> ((V 42%nat) + 4096 <= 65536 \/ 65536 + 6434816 <= (V 42%nat)) -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147449560) 1320 ->
  L5.img_clear M 65536 880640 -> L5.img_clear M 892736 892768 -> L5.u64_at RSEGS M 874680 908088 -> L5.u64_at RSEGS M 908088 2147450880 ->
  L5.u64_at RSEGS M 874688 911400 -> L5.u64_at RSEGS M 911400 0 -> L5.u64_at RSEGS M 874696 911408 -> L5.u64_at RSEGS M 911408 0 ->
  L5.u64_at RSEGS M 874704 911392 -> L5.u64_at RSEGS M 911392 140737488355327 -> L5.u64_at RSEGS M 877600 911385 -> L5.u8_at RSEGS M 911385 1 ->
  L5.u64_at RSEGS M 882712 834348 -> L5.u64_at RSEGS M 882704 833320 -> L5.u8_at RSEGS M 911384 1 -> L5.u64_at RSEGS M 882488 836764 ->
  L5.u64_at RSEGS M 6360320 6360360 -> L5.u64_at RSEGS M 6360368 6362376 -> L5.u8_at RSEGS M 906144 1 -> L5.u32_at RSEGS M 906148 0 ->
  L5.u64_at RSEGS M 6360240 6496432 -> L5.u64_at RSEGS M 874664 1504872 -> L5.u8_at RSEGS M 1505009 1 -> L5.u64_at RSEGS M 874760 1496536 ->
  L5.u32_at RSEGS M 1496536 0 -> L5.u64_at RSEGS M 878208 8 -> L5.u64_at RSEGS M 6496432 (V 40%nat) -> L5.u64_at RSEGS M ((V 40%nat) + 152) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 41%nat) + 48) (V 43%nat) -> L5.u64_at RSEGS M ((V 41%nat) + 56) (V 44%nat) -> L5.u64_at RSEGS M 6360336 (V 42%nat) -> L5.u64_at RSEGS M ((V 42%nat) + 24) 6360328 ->
  4096 <= (V 40%nat) <= 140737479966560 -> 4096 <= (V 41%nat) <= 140737479966656 -> 4096 <= (V 42%nat) <= 140737479962624 -> L5.u64_at RSEGS M ((V 10%nat) - 16) 0 ->
  L5.u64_at RSEGS M 6491464 (V 33%nat) -> L5.u64_at RSEGS M 6492064 (V 32%nat) -> L5.u64_at RSEGS M (V 32%nat) 3 -> L5.u64_at RSEGS M ((V 32%nat) + 8) 65600 ->
  L5.u64_at RSEGS M ((V 32%nat) + 16) 4 -> L5.u64_at RSEGS M ((V 32%nat) + 24) 56 -> L5.u64_at RSEGS M ((V 32%nat) + 32) 5 -> L5.u64_at RSEGS M ((V 32%nat) + 40) 11 ->
  L5.u64_at RSEGS M ((V 32%nat) + 48) 16 -> L5.u64_at RSEGS M ((V 32%nat) + 56) (V 39%nat) -> L5.u64_at RSEGS M ((V 32%nat) + 64) 6 -> L5.u64_at RSEGS M ((V 32%nat) + 72) 4096 ->
  L5.u64_at RSEGS M ((V 32%nat) + 80) 11 -> L5.u64_at RSEGS M ((V 32%nat) + 88) (V 34%nat) -> L5.u64_at RSEGS M ((V 32%nat) + 96) 12 -> L5.u64_at RSEGS M ((V 32%nat) + 104) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 32%nat) + 112) 23 -> L5.u64_at RSEGS M ((V 32%nat) + 120) 0 -> L5.u64_at RSEGS M ((V 32%nat) + 128) 25 -> L5.u64_at RSEGS M ((V 32%nat) + 136) (V 36%nat) ->
  L5.u64_at RSEGS M ((V 32%nat) + 144) 0 -> L5.u64_at RSEGS M ((V 10%nat) - 8) ((V 2%nat) + 1216) -> L5.u64_at RSEGS M ((V 10%nat) - 32) 4849336966747728640 -> L5.u64_at RSEGS M ((V 2%nat) + 120) 588096 ->
  L5.u64_at RSEGS M ((V 2%nat) + 112) ((V 2%nat) + 256) -> L5.u64_at RSEGS M ((V 2%nat) + 104) ((V 2%nat) + 128) -> L5.u64_at RSEGS M ((V 2%nat) + 96) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 88) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 80) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 72) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 64) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 56) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 48) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 32) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 248) 599896 ->
  L5.u64_at RSEGS M ((V 2%nat) + 240) ((V 2%nat) + 608) -> L5.u64_at RSEGS M ((V 2%nat) + 232) ((V 2%nat) + 256) -> L5.u64_at RSEGS M ((V 2%nat) + 224) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 216) (V 55%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 208) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 200) (V 57%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 192) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 184) (V 59%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 176) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 168) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 160) (V 62%nat) -> L5.u8_at RSEGS M 6360113 1 ->
  L5.u8_at RSEGS M 6360114 0 -> L5.u8_at RSEGS M 6360115 1 -> L5.u8_at RSEGS M 6360116 0 -> L5.u8_at RSEGS M 6360117 1 ->
  L5.u8_at RSEGS M 6360118 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 10560) <= bv_unsigned a < ((V 2%nat) - 10560) + 10560) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 10560) <= i < ((V 2%nat) - 10560) + 10560) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x90438 M) (st fx' R' 0x930b8 M')
        /\ (forall x, In x KS_ue3r1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602296
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 256)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) + 608)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) + 256)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 62%nat)).
Proof.
  intros [HV2l HV2r] [HV10l HV10r] [HV32l HV32r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV39l HV39r] [HV40l HV40r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] [HV52l HV52r] [HV53l HV53r] [HV54l HV54r] [HV55l HV55r] [HV56l HV56r] [HV57l HV57r] [HV58l HV58r] [HV59l HV59r] [HV60l HV60r] [HV61l HV61r] [HV62l HV62r] G2 G3 G4 G8 G10 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 K8 K9 [K10l K10r] K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 [K64l K64r] [K65l K65r] [K66l K66r] K67 K68 K69 K70 K71 K72 K73 K74 K75 K76 K77 K78 K79 K80 K81 K82 K83 K84 K85 K86 K87 K88 K89 K90 K91 K92 K93 K94 K95 K96 K97 K98 K99 K100 K101 K102 K103 K104 K105 K106 K107 K108 K109 K110 K111 K112 K113 K114 K115 K116 K117 K118 K119 K120.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 10%nat => Z_to_bv 64 (V 10%nat) | 32%nat => Z_to_bv 64 (V 32%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | 55%nat => Z_to_bv 64 (V 55%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 10%nat => (V 10%nat) | 32%nat => (V 32%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | 54%nat => (V 54%nat) | 55%nat => (V 55%nat) | 56%nat => (V 56%nat) | 57%nat => (V 57%nat) | 58%nat => (V 58%nat) | 59%nat => (V 59%nat) | 60%nat => (V 60%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E Pue3r1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pue3r1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pue3r1.kn0).
  { unfold know_ok, Pue3r1.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K14 K18 K21 K22 K23 K28 K64l K64r) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K16 K20 K23 K25 K26 K30 K66l K66r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K14 K18 K21 K22 K23 K28 K64l K64r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K16 K20 K23 K25 K26 K30 K66l K66r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K14 K18 K21 K22 K23 K28 K64l K64r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K14 K18 K21 K22 K23 K28 K64l K64r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K14 K18 K21 K22 K23 K28 K64l K64r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K16 K20 K23 K25 K26 K30 K66l K66r) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K16 K20 K23 K25 K26 K30 K66l K66r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K16 K20 K23 K25 K26 K30 K66l K66r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K14 K18 K21 K22 K23 K28 K64l K64r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K16 K20 K23 K25 K26 K30 K66l K66r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K14 K18 K21 K22 K23 K28 K64l K64r) | clear; lia | clear; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K14 K18 K21 K22 K23 K28 K64l K64r) | evalEk ZA ltac:(clear - HV41l HV41r K15 K19 K22 K24 K25 K29 K65l K65r) | clear - HV40l HV40r K14 K18 K21 K22 K23 K28 K64l K64r; lia | clear - HV40l HV40r K14 K18 K21 K22 K23 K28 K64l K64r; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV41l HV41r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV41l HV41r K15 K19 K22 K24 K25 K29 K65l K65r; lia | clear - HV41l HV41r K15 K19 K22 K24 K25 K29 K65l K65r; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV41l HV41r K15 K19 K22 K24 K25 K29 K65l K65r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV41l HV41r K15 K19 K22 K24 K25 K29 K65l K65r; lia | clear - HV41l HV41r K15 K19 K22 K24 K25 K29 K65l K65r; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K16 K20 K23 K25 K26 K30 K66l K66r) | clear; lia | clear; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV42l HV42r K16 K20 K23 K25 K26 K30 K66l K66r) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K16 K20 K23 K25 K26 K30 K66l K66r; lia | clear - HV42l HV42r K16 K20 K23 K25 K26 K30 K66l K66r; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K14 K18 K21 K22 K23 K28 K64l K64r) | exact (conj K64l K64r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K15 K19 K22 K24 K25 K29 K65l K65r) | exact (conj K65l K65r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K16 K20 K23 K25 K26 K30 K66l K66r) | exact (conj K66l K66r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r) | clear; lia | clear; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | clear; lia | clear; lia | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K70]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K71]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K72]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K73]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K74]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K75]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K76]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K77]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K78]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K79]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K80]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K81]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K82]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K83]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K84]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K85]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K86]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear - HV36l HV36r) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K87]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20) | evalEk ZA ltac:(clear) | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | clear - HV32l HV32r K10l K10r K13 K17 K18 K19 K20; lia | exactA K88]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | exactA K89]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | clear - HV10l HV10r K4l K4r K8 K12 K13 K14 K15 K16 K27; lia | exactA K90]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K91]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K92]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K93]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K94]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K95]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K96]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K97]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K98]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K99]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K100]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K101]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K102]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K103]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K104]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K105]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K106]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K107]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K108]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K109]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K110]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K111]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K112]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K113]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26; lia | exactA K114]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K115]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K116]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K117]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K118]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K119]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K120]. }
    apply Forall_nil. }
  destruct (Pue3r1.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pue3r1.NX0 with 63%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 10560) <= bv_unsigned a < ((V 2%nat) - 10560) + 10560) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pue3r1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K12 K17 K21 K24 K26 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pue3r1.ps0) with 0x930b8 in Hms. change (SR.ps_regs Pue3r1.ps0) with (map (fun i => (i, nth i Pue3r1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pue3r1.ps0) with Pue3r1.cells0 in Hcells. unfold Pue3r1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pue3r1.regs0 Pue3r1.regs_out0 63 KS_ue3r1 KS_ue3r1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pue3r1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pue3r1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3r1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pue3r1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3r1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pue3r1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3r1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pue3r1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3r1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pue3r1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3r1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pue3r1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3r1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pue3r1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3r1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pue3r1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3r1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pue3r1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3r1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pue3r1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3r1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pue3r1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3r1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pue3r1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue3r1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pue3r1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pue3r1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pue3r1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End L5AE3P6.
