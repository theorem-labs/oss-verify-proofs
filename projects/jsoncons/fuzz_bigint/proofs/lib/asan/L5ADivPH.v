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
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegZ_v5P4gi LibSegZ_v5P4gd LibSegZ_v5P4hi LibSegZ_v5P4hd LibSegZ_v5HTh LibSegZ_v5HTg LibSegZ_v5H1i LibSegZ_v5H3 LibSegZ_v5H4i.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia.
Local Ltac nodj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac nodisj := L5FastLia.prune_arith; repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac lia := first [ solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ] | solve [ nodisj; L5FastLia.lia_st ] | L5FastLia.plia ].   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5ADIVPH.
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
Module Pv5P4gi := LibSegZ_v5P4gi.
Definition KS_v5P4gi : list nat := Eval vm_compute in (BG.kept_list 80 Pv5P4gi.regs0 Pv5P4gi.regs_out0).
Lemma KS_v5P4gi_ok : BG.kept_ok 80 Pv5P4gi.regs0 Pv5P4gi.regs_out0 KS_v5P4gi = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5P4gi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 10) = Z_to_bv 64 (V 64%nat) -> getr R (reg 19) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 (V 63%nat) -> getr R (reg 22) = Z_to_bv 64 (V 57%nat) -> getr R (reg 24) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487584 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 352) + 352 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 352)) -> (((V 2%nat) - 352) + 352 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 352)) -> 4096 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 352) + 352 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 352)) ->
  ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 33%nat) / 8) + 2147450880)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) ->
  ((((V 33%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 352) \/ ((V 2%nat) - 352) + 352 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 248) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 200) 2147450880 ->
  0 <= (V 64%nat) <= 1 -> 0 <= (V 57%nat) <= 1 -> 0 <= (V 35%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 40%nat) + 104) (V 65%nat) ->
  2 <= (V 63%nat) <= 18446744073709551615 -> 0 <= (V 65%nat) <= 18446744073709551615 -> L5.u8_at RSEGS M ((V 40%nat) + 96) (V 60%nat) -> 0 <= (V 60%nat) <= 255 ->
  Z.testbit (V 60%nat) 0 = false -> L5.u8_at RSEGS M (V 33%nat) (V 56%nat) -> 0 <= (V 56%nat) <= 255 -> Z.testbit (V 56%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 272) <= bv_unsigned a < ((V 2%nat) - 272) + 8) -> ~ (((V 2%nat) - 312) <= bv_unsigned a < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 272) <= i < ((V 2%nat) - 272) + 8) -> ~ (((V 2%nat) - 312) <= i < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= i < ((V 2%nat) - 296) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x92374 M) (st fx' R' 0x926d8 M')
        /\ (forall x, In x KS_v5P4gi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 40%nat) + 112)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) (V 57%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) ((V 40%nat) + 96)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV40l HV40r] [HV41l HV41r] [HV56l HV56r] [HV57l HV57r] [HV58l HV58r] [HV60l HV60r] [HV63l HV63r] [HV64l HV64r] [HV65l HV65r] G1 G2 G8 G9 G10 G19 G20 G22 G24 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 [K32l K32r] [K33l K33r] [K34l K34r] K35 [K36l K36r] [K37l K37r] K38 [K39l K39r] K40 K41 [K42l K42r] K43.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 56%nat => (V 56%nat) | 57%nat => (V 57%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 63%nat => (V 63%nat) | 64%nat => (V 64%nat) | 65%nat => (V 65%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 66%nat. }
  assert (HR: regs_ok E Pv5P4gi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5P4gi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5P4gi.kn0).
  { unfold know_ok, Pv5P4gi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K34l K34r; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K32l K32r; nodj) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K33l K33r; nodj) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K34l K34r; nodj) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV65l HV65r K37l K37r; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV63l HV63r K36l K36r; nodj) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K37l K37r; nodj) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV60l HV60r K39l K39r K40; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | byte_tac ltac:(clear - HV60l HV60r K39l K39r K40) | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K39l K39r K40; nodj) | exact (conj K39l K39r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K39l K39r K40; nodj) | clear; lia | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K39l K39r K40; lia) K40); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear - HV56l HV56r K42l K42r K43; nodj) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | byte_tac ltac:(clear - HV56l HV56r K42l K42r K43) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K42l K42r K43; nodj) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV56l HV56r K42l K42r K43; nodj) | clear; lia | rewrite (L5K.land1_bit0_false (V 56%nat) ltac:(clear - HV56l HV56r K42l K42r K43; lia) K43); clear; lia]. }
    apply Forall_nil. }
  destruct (Pv5P4gi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5P4gi.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 272) <= bv_unsigned a < ((V 2%nat) - 272) + 8) -> ~ (((V 2%nat) - 312) <= bv_unsigned a < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pv5P4gi.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5P4gi.ps0) with 0x926d8 in Hms. change (SR.ps_regs Pv5P4gi.ps0) with (map (fun i => (i, nth i Pv5P4gi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5P4gi.ps0) with Pv5P4gi.cells0 in Hcells. unfold Pv5P4gi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5P4gi.regs0 Pv5P4gi.regs_out0 80 KS_v5P4gi KS_v5P4gi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5P4gi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5P4gi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4gi.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5P4gi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4gi.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5P4gi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4gi.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5P4gi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4gi.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pv5P4gi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4gi.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pv5P4gi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4gi.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5P4gi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4gi.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pv5P4gi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear - HV57l HV57r K33l K33r; nodj) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5P4gd := LibSegZ_v5P4gd.
Definition KS_v5P4gd : list nat := Eval vm_compute in (BG.kept_list 80 Pv5P4gd.regs0 Pv5P4gd.regs_out0).
Lemma KS_v5P4gd_ok : BG.kept_ok 80 Pv5P4gd.regs0 Pv5P4gd.regs_out0 KS_v5P4gd = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5P4gd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 10) = Z_to_bv 64 (V 64%nat) -> getr R (reg 19) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 (V 63%nat) -> getr R (reg 22) = Z_to_bv 64 (V 57%nat) -> getr R (reg 24) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487584 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 352) + 352 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 352)) -> (((V 2%nat) - 352) + 352 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 352)) -> 4096 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 352) + 352 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 352)) ->
  ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 33%nat) / 8) + 2147450880)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) ->
  ((((V 33%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 352) \/ ((V 2%nat) - 352) + 352 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 248) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 200) 2147450880 ->
  0 <= (V 64%nat) <= 1 -> 0 <= (V 57%nat) <= 1 -> 0 <= (V 35%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 40%nat) + 104) (V 65%nat) ->
  2 <= (V 63%nat) <= 18446744073709551615 -> 0 <= (V 65%nat) <= 18446744073709551615 -> L5.u8_at RSEGS M ((V 40%nat) + 96) (V 60%nat) -> 0 <= (V 60%nat) <= 255 ->
  Z.testbit (V 60%nat) 0 = true -> L5.u64_at RSEGS M ((V 40%nat) + 120) (V 61%nat) -> 4096 <= (V 61%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 40%nat) + 112) (V 62%nat) ->
  1 <= (V 62%nat) <= 134217728 -> L5.u8_at RSEGS M (V 33%nat) (V 56%nat) -> 0 <= (V 56%nat) <= 255 -> Z.testbit (V 56%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 33%nat) + 24) (V 66%nat) -> 4096 <= (V 66%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 272) <= bv_unsigned a < ((V 2%nat) - 272) + 8) -> ~ (((V 2%nat) - 312) <= bv_unsigned a < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 272) <= i < ((V 2%nat) - 272) + 8) -> ~ (((V 2%nat) - 312) <= i < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= i < ((V 2%nat) - 296) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x92374 M) (st fx' R' 0x926d8 M')
        /\ (forall x, In x KS_v5P4gd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) (V 57%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) ((V 40%nat) + 96)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV40l HV40r] [HV41l HV41r] [HV56l HV56r] [HV57l HV57r] [HV58l HV58r] [HV60l HV60r] [HV61l HV61r] [HV62l HV62r] [HV63l HV63r] [HV64l HV64r] [HV65l HV65r] [HV66l HV66r] G1 G2 G8 G9 G10 G19 G20 G22 G24 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 [K32l K32r] [K33l K33r] [K34l K34r] K35 [K36l K36r] [K37l K37r] K38 [K39l K39r] K40 K41 [K42l K42r] K43 [K44l K44r] K45 [K46l K46r] K47 K48 [K49l K49r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 56%nat => (V 56%nat) | 57%nat => (V 57%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 63%nat => (V 63%nat) | 64%nat => (V 64%nat) | 65%nat => (V 65%nat) | 66%nat => (V 66%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 67%nat. }
  assert (HR: regs_ok E Pv5P4gd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5P4gd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5P4gd.kn0).
  { unfold know_ok, Pv5P4gd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K34l K34r; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K32l K32r; nodj) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K33l K33r; nodj) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K34l K34r; nodj) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV65l HV65r K37l K37r; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV63l HV63r K36l K36r; nodj) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K37l K37r; nodj) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV60l HV60r K39l K39r K40; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | byte_tac ltac:(clear - HV60l HV60r K39l K39r K40) | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K39l K39r K40; nodj) | exact (conj K39l K39r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K39l K39r K40; nodj) | clear; lia | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K39l K39r K40; lia) K40); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV61l HV61r K42l K42r; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K42l K42r; nodj) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV62l HV62r K44l K44r; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K44l K44r; nodj) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear - HV56l HV56r K46l K46r K47; nodj) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | byte_tac ltac:(clear - HV56l HV56r K46l K46r K47) | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K46l K46r K47; nodj) | exact (conj K46l K46r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV56l HV56r K46l K46r K47; nodj) | clear; lia | rewrite (L5K.land1_bit0_true (V 56%nat) ltac:(clear - HV56l HV56r K46l K46r K47; lia) K47); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear - HV66l HV66r K49l K49r; nodj) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K49l K49r; nodj) | exact (conj K49l K49r)]. }
    apply Forall_nil. }
  destruct (Pv5P4gd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5P4gd.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 272) <= bv_unsigned a < ((V 2%nat) - 272) + 8) -> ~ (((V 2%nat) - 312) <= bv_unsigned a < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pv5P4gd.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5P4gd.ps0) with 0x926d8 in Hms. change (SR.ps_regs Pv5P4gd.ps0) with (map (fun i => (i, nth i Pv5P4gd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5P4gd.ps0) with Pv5P4gd.cells0 in Hcells. unfold Pv5P4gd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5P4gd.regs0 Pv5P4gd.regs_out0 80 KS_v5P4gd KS_v5P4gd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5P4gd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5P4gd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4gd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5P4gd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4gd.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5P4gd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4gd.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5P4gd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4gd.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pv5P4gd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4gd.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pv5P4gd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4gd.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5P4gd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4gd.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pv5P4gd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear - HV57l HV57r K33l K33r; nodj) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5P4hi := LibSegZ_v5P4hi.
Definition KS_v5P4hi : list nat := Eval vm_compute in (BG.kept_list 80 Pv5P4hi.regs0 Pv5P4hi.regs_out0).
Lemma KS_v5P4hi_ok : BG.kept_ok 80 Pv5P4hi.regs0 Pv5P4hi.regs_out0 KS_v5P4hi = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5P4hi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 10) = Z_to_bv 64 (V 64%nat) -> getr R (reg 19) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 22) = Z_to_bv 64 (V 57%nat) -> getr R (reg 24) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487584 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 352) + 352 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 352)) -> (((V 2%nat) - 352) + 352 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 352)) -> 4096 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 352) + 352 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 352)) ->
  ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 33%nat) / 8) + 2147450880)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) ->
  ((((V 33%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 352) \/ ((V 2%nat) - 352) + 352 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 248) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 200) 2147450880 ->
  0 <= (V 64%nat) <= 1 -> 0 <= (V 57%nat) <= 1 -> 0 <= (V 35%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 40%nat) + 104) (V 65%nat) ->
  2 <= (V 65%nat) <= 18446744073709551615 -> L5.u8_at RSEGS M ((V 40%nat) + 96) (V 60%nat) -> 0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = false ->
  L5.u8_at RSEGS M (V 33%nat) (V 56%nat) -> 0 <= (V 56%nat) <= 255 -> Z.testbit (V 56%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 272) <= bv_unsigned a < ((V 2%nat) - 272) + 8) -> ~ (((V 2%nat) - 312) <= bv_unsigned a < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 272) <= i < ((V 2%nat) - 272) + 8) -> ~ (((V 2%nat) - 312) <= i < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= i < ((V 2%nat) - 296) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x92374 M) (st fx' R' 0x9267c M')
        /\ (forall x, In x KS_v5P4hi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 40%nat) + 112)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) (V 57%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) ((V 40%nat) + 96)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV40l HV40r] [HV41l HV41r] [HV56l HV56r] [HV57l HV57r] [HV58l HV58r] [HV60l HV60r] [HV64l HV64r] [HV65l HV65r] G1 G2 G8 G9 G10 G19 G20 G22 G24 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 [K32l K32r] [K33l K33r] [K34l K34r] K35 [K36l K36r] K37 [K38l K38r] K39 K40 [K41l K41r] K42.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 56%nat => (V 56%nat) | 57%nat => (V 57%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 64%nat => (V 64%nat) | 65%nat => (V 65%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 66%nat. }
  assert (HR: regs_ok E Pv5P4hi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5P4hi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5P4hi.kn0).
  { unfold know_ok, Pv5P4hi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K34l K34r; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K32l K32r; nodj) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K33l K33r; nodj) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K34l K34r; nodj) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV65l HV65r K36l K36r; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K36l K36r; nodj) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV60l HV60r K38l K38r K39; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | byte_tac ltac:(clear - HV60l HV60r K38l K38r K39) | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K38l K38r K39; nodj) | exact (conj K38l K38r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K38l K38r K39; nodj) | clear; lia | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K38l K38r K39; lia) K39); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear - HV56l HV56r K41l K41r K42; nodj) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | byte_tac ltac:(clear - HV56l HV56r K41l K41r K42) | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K41l K41r K42; nodj) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV56l HV56r K41l K41r K42; nodj) | clear; lia | rewrite (L5K.land1_bit0_false (V 56%nat) ltac:(clear - HV56l HV56r K41l K41r K42; lia) K42); clear; lia]. }
    apply Forall_nil. }
  destruct (Pv5P4hi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5P4hi.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 272) <= bv_unsigned a < ((V 2%nat) - 272) + 8) -> ~ (((V 2%nat) - 312) <= bv_unsigned a < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pv5P4hi.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5P4hi.ps0) with 0x9267c in Hms. change (SR.ps_regs Pv5P4hi.ps0) with (map (fun i => (i, nth i Pv5P4hi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5P4hi.ps0) with Pv5P4hi.cells0 in Hcells. unfold Pv5P4hi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5P4hi.regs0 Pv5P4hi.regs_out0 80 KS_v5P4hi KS_v5P4hi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5P4hi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5P4hi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4hi.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5P4hi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4hi.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5P4hi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4hi.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5P4hi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4hi.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pv5P4hi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4hi.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pv5P4hi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4hi.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5P4hi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4hi.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pv5P4hi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear - HV57l HV57r K33l K33r; nodj) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5P4hd := LibSegZ_v5P4hd.
Definition KS_v5P4hd : list nat := Eval vm_compute in (BG.kept_list 80 Pv5P4hd.regs0 Pv5P4hd.regs_out0).
Lemma KS_v5P4hd_ok : BG.kept_ok 80 Pv5P4hd.regs0 Pv5P4hd.regs_out0 KS_v5P4hd = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5P4hd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 10) = Z_to_bv 64 (V 64%nat) -> getr R (reg 19) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 22) = Z_to_bv 64 (V 57%nat) -> getr R (reg 24) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487584 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 352) + 352 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 352)) -> (((V 2%nat) - 352) + 352 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 352)) -> 4096 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 352) + 352 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 352)) ->
  ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 33%nat) / 8) + 2147450880)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) ->
  ((((V 33%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 352) \/ ((V 2%nat) - 352) + 352 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 248) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 208) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 200) 2147450880 ->
  0 <= (V 64%nat) <= 1 -> 0 <= (V 57%nat) <= 1 -> 0 <= (V 35%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 40%nat) + 104) (V 65%nat) ->
  2 <= (V 65%nat) <= 18446744073709551615 -> L5.u8_at RSEGS M ((V 40%nat) + 96) (V 60%nat) -> 0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 40%nat) + 120) (V 61%nat) -> 4096 <= (V 61%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 40%nat) + 112) (V 62%nat) -> 1 <= (V 62%nat) <= 134217728 ->
  L5.u8_at RSEGS M (V 33%nat) (V 56%nat) -> 0 <= (V 56%nat) <= 255 -> Z.testbit (V 56%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 66%nat) ->
  4096 <= (V 66%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 272) <= bv_unsigned a < ((V 2%nat) - 272) + 8) -> ~ (((V 2%nat) - 312) <= bv_unsigned a < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 272) <= i < ((V 2%nat) - 272) + 8) -> ~ (((V 2%nat) - 312) <= i < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= i < ((V 2%nat) - 296) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x92374 M) (st fx' R' 0x9267c M')
        /\ (forall x, In x KS_v5P4hd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 61%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 296) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 312) (V 57%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 272) ((V 40%nat) + 96)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV40l HV40r] [HV41l HV41r] [HV56l HV56r] [HV57l HV57r] [HV58l HV58r] [HV60l HV60r] [HV61l HV61r] [HV62l HV62r] [HV64l HV64r] [HV65l HV65r] [HV66l HV66r] G1 G2 G8 G9 G10 G19 G20 G22 G24 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 [K32l K32r] [K33l K33r] [K34l K34r] K35 [K36l K36r] K37 [K38l K38r] K39 K40 [K41l K41r] K42 [K43l K43r] K44 [K45l K45r] K46 K47 [K48l K48r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 66%nat => Z_to_bv 64 (V 66%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 56%nat => (V 56%nat) | 57%nat => (V 57%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | 64%nat => (V 64%nat) | 65%nat => (V 65%nat) | 66%nat => (V 66%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 67%nat. }
  assert (HR: regs_ok E Pv5P4hd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5P4hd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5P4hd.kn0).
  { unfold know_ok, Pv5P4hd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K34l K34r; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K32l K32r; nodj) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K33l K33r; nodj) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K34l K34r; nodj) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV65l HV65r K36l K36r; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K36l K36r; nodj) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV60l HV60r K38l K38r K39; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | byte_tac ltac:(clear - HV60l HV60r K38l K38r K39) | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K38l K38r K39; nodj) | exact (conj K38l K38r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K38l K38r K39; nodj) | clear; lia | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K38l K38r K39; lia) K39); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV61l HV61r K41l K41r; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K41l K41r; nodj) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV62l HV62r K43l K43r; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K43l K43r; nodj) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear - HV56l HV56r K45l K45r K46; nodj) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | byte_tac ltac:(clear - HV56l HV56r K45l K45r K46) | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K45l K45r K46; nodj) | exact (conj K45l K45r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV56l HV56r K45l K45r K46; nodj) | clear; lia | rewrite (L5K.land1_bit0_true (V 56%nat) ltac:(clear - HV56l HV56r K45l K45r K46; lia) K46); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear - HV66l HV66r K48l K48r; nodj) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K48l K48r; nodj) | exact (conj K48l K48r)]. }
    apply Forall_nil. }
  destruct (Pv5P4hd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5P4hd.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 272) <= bv_unsigned a < ((V 2%nat) - 272) + 8) -> ~ (((V 2%nat) - 312) <= bv_unsigned a < ((V 2%nat) - 312) + 8) -> ~ (((V 2%nat) - 296) <= bv_unsigned a < ((V 2%nat) - 296) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pv5P4hd.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5P4hd.ps0) with 0x9267c in Hms. change (SR.ps_regs Pv5P4hd.ps0) with (map (fun i => (i, nth i Pv5P4hd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5P4hd.ps0) with Pv5P4hd.cells0 in Hcells. unfold Pv5P4hd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5P4hd.regs0 Pv5P4hd.regs_out0 80 KS_v5P4hd KS_v5P4hd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5P4hd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5P4hd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4hd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5P4hd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4hd.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5P4hd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4hd.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5P4hd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4hd.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pv5P4hd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4hd.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pv5P4hd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4hd.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5P4hd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5P4hd.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pv5P4hd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear - HV57l HV57r K33l K33r; nodj) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5HTh := LibSegZ_v5HTh.
Definition KS_v5HTh : list nat := Eval vm_compute in (BG.kept_list 80 Pv5HTh.regs0 Pv5HTh.regs_out0).
Lemma KS_v5HTh_ok : BG.kept_ok 80 Pv5HTh.regs0 Pv5HTh.regs_out0 KS_v5HTh = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5HTh_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 10) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 22) = Z_to_bv 64 (V 35%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 48) ->
  140735332487584 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 352) + 352 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 352)) -> (((V 2%nat) - 352) + 352 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 352)) -> 4096 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 352) + 352 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 352)) ->
  ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 33%nat) / 8) + 2147450880)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) ->
  ((((V 33%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 352) \/ ((V 2%nat) - 352) + 352 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 296) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 200) 2147450880 -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450884) 4 ->
  L5.u64_at RSEGS M ((V 40%nat) + 48) (V 68%nat) -> 0 <= (V 68%nat) <= 4294967295 -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 67%nat) -> 0 <= (V 67%nat) <= 18446744073709551615 ->
  0 <= (V 35%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x9267c M) (st fx' R' 0x8f810 M')
        /\ (forall x, In x KS_v5HTh -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 599728
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 40%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV67l HV67r] [HV68l HV68r] G1 G2 G8 G9 G10 G22 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 [K33l K33r] K34 [K35l K35r] [K36l K36r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 67%nat => (V 67%nat) | 68%nat => (V 68%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E Pv5HTh.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5HTh.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5HTh.kn0).
  { unfold know_ok, Pv5HTh.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV68l HV68r K33l K33r; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K33l K33r; nodj) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear - HV67l HV67r K35l K35r; nodj) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K35l K35r; nodj) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K36l K36r; nodj) | exact (conj K36l K36r)]. }
    apply Forall_nil. }
  destruct (Pv5HTh.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5HTh.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pv5HTh.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5HTh.ps0) with 0x8f810 in Hms. change (SR.ps_regs Pv5HTh.ps0) with (map (fun i => (i, nth i Pv5HTh.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5HTh.ps0) with Pv5HTh.cells0 in Hcells. unfold Pv5HTh.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5HTh.regs0 Pv5HTh.regs_out0 80 KS_v5HTh KS_v5HTh_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5HTh.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5HTh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5HTh.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5HTh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5HTh.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5HTh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5HTh.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5HTh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5HTh.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pv5HTh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5HTh.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5HTh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pv5HTh.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pv5HTh.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5HTg := LibSegZ_v5HTg.
Definition KS_v5HTg : list nat := Eval vm_compute in (BG.kept_list 80 Pv5HTg.regs0 Pv5HTg.regs_out0).
Lemma KS_v5HTg_ok : BG.kept_ok 80 Pv5HTg.regs0 Pv5HTg.regs_out0 KS_v5HTg = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5HTg_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 10) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 22) = Z_to_bv 64 (V 35%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 48) ->
  140735332487584 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 352) + 352 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 352)) -> (((V 2%nat) - 352) + 352 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 352)) -> 4096 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 352) + 352 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 352)) ->
  ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 33%nat) / 8) + 2147450880)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) ->
  ((((V 33%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 352) \/ ((V 2%nat) - 352) + 352 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 296) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 200) 2147450880 -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450884) 4 ->
  L5.u64_at RSEGS M ((V 40%nat) + 48) (V 68%nat) -> 4294967296 <= (V 68%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 67%nat) -> 0 <= (V 67%nat) <= 18446744073709551615 ->
  0 <= (V 35%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x9267c M) (st fx' R' 0x926d8 M')
        /\ (forall x, In x KS_v5HTg -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 68%nat) / 4294967296)
        /\ getr R' (reg 12) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 68%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV67l HV67r] [HV68l HV68r] G1 G2 G8 G9 G10 G22 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 [K33l K33r] K34 [K35l K35r] [K36l K36r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 67%nat => Z_to_bv 64 (V 67%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 67%nat => (V 67%nat) | 68%nat => (V 68%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 69%nat. }
  assert (HR: regs_ok E Pv5HTg.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5HTg.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5HTg.kn0).
  { unfold know_ok, Pv5HTg.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV68l HV68r K33l K33r; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K33l K33r; nodj) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear - HV67l HV67r K35l K35r; nodj) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K35l K35r; nodj) | exact (conj K35l K35r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K36l K36r; nodj) | exact (conj K36l K36r)]. }
    apply Forall_nil. }
  destruct (Pv5HTg.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5HTg.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pv5HTg.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5HTg.ps0) with 0x926d8 in Hms. change (SR.ps_regs Pv5HTg.ps0) with (map (fun i => (i, nth i Pv5HTg.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5HTg.ps0) with Pv5HTg.cells0 in Hcells. unfold Pv5HTg.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5HTg.regs0 Pv5HTg.regs_out0 80 KS_v5HTg KS_v5HTg_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5HTg.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5HTg.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5HTg.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5HTg.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pv5HTg.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pv5HTg.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5H1i := LibSegZ_v5H1i.
Definition KS_v5H1i : list nat := Eval vm_compute in (BG.kept_list 80 Pv5H1i.regs0 Pv5H1i.regs_out0).
Lemma KS_v5H1i_ok : BG.kept_ok 80 Pv5H1i.regs0 Pv5H1i.regs_out0 KS_v5H1i = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5H1i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 22) = Z_to_bv 64 (V 35%nat) -> getr R (reg 24) = Z_to_bv 64 2 ->
  140735332487584 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 352) + 352 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 352)) -> (((V 2%nat) - 352) + 352 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 352)) -> 4096 <= (V 35%nat) <= 140737488355296 ->
  aligned (V 35%nat) 8 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) ->
  ((V 35%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 35%nat)) -> ((V 35%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 35%nat)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 35%nat) / 8) + 2147450880)) ->
  ((((V 35%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 352) \/ ((V 2%nat) - 352) + 352 <= (((V 35%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 200) 2147450880 -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 ->
  Z.testbit (V 69%nat) 0 = false -> 4096 <= (V 33%nat) <= 140737488355296 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x926b0 M) (st fx' R' 0x92aec M')
        /\ (forall x, In x KS_v5H1i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 35%nat) + 24)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 35%nat) + 24)
        /\ getr R' (reg 20) = Z_to_bv 64 (((V 35%nat) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 26) = Z_to_bv 64 2147450880).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV69l HV69r] G1 G2 G8 G9 G21 G22 G24 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 [K31l K31r] K32 [K33l K33r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 69%nat => (V 69%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E Pv5H1i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5H1i.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5H1i.kn0).
  { unfold know_ok, Pv5H1i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; nodj) | evalEk ZA ltac:(clear - HV69l HV69r K31l K31r K32; nodj) | clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | clear - HV35l HV35r K19l K19r K21 K23 K24 K25 K26 K27 K28; lia | byte_tac ltac:(clear - HV69l HV69r K31l K31r K32) | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K31l K31r K32; nodj) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV69l HV69r K31l K31r K32; nodj) | clear; lia | rewrite (L5K.land1_bit0_false (V 69%nat) ltac:(clear - HV69l HV69r K31l K31r K32; lia) K32); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K33l K33r; nodj) | exact (conj K33l K33r)]. }
    apply Forall_nil. }
  destruct (Pv5H1i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5H1i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pv5H1i.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5H1i.ps0) with 0x92aec in Hms. change (SR.ps_regs Pv5H1i.ps0) with (map (fun i => (i, nth i Pv5H1i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5H1i.ps0) with Pv5H1i.cells0 in Hcells. unfold Pv5H1i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5H1i.regs0 Pv5H1i.regs_out0 80 KS_v5H1i KS_v5H1i_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5H1i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5H1i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5H1i.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5H1i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5H1i.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5H1i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5H1i.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pv5H1i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5H1i.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pv5H1i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5H1i.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pv5H1i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pv5H1i.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pv5H1i.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5H3 := LibSegZ_v5H3.
Definition KS_v5H3 : list nat := Eval vm_compute in (BG.kept_list 80 Pv5H3.regs0 Pv5H3.regs_out0).
Lemma KS_v5H3_ok : BG.kept_ok 80 Pv5H3.regs0 Pv5H3.regs_out0 KS_v5H3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5H3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 22) = Z_to_bv 64 (V 71%nat) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487584 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 352) + 352 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 352)) -> (((V 2%nat) - 352) + 352 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 352)) -> L5.u64_at RSEGS M ((V 2%nat) - 240) (((V 40%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 256) (V 36%nat) -> 0 <= (V 71%nat) <= 18446744073709551615 -> 0 <= (V 36%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 40%nat) / 8) + 2147450924) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450924) + 4) -> ~ (((V 40%nat) + 352) <= bv_unsigned a < ((V 40%nat) + 352) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 40%nat) / 8) + 2147450924) <= i < (((V 40%nat) / 8) + 2147450924) + 4) -> ~ (((V 40%nat) + 352) <= i < ((V 40%nat) + 352) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x92b70 M) (st fx' R' 0x8f690 M')
        /\ (forall x, In x KS_v5H3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 601000
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 352)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 40%nat) + 352)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 376) 0
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 368) (V 71%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 360) (if 0 <? (V 71%nat) then 1 else 0)
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 352) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450927) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450926) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450925) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450924) 0
        /\ L5.defined M' (V 40%nat) 352
        /\ L5.defined M' ((V 40%nat) + 353) 7
        /\ L5.defined M' ((V 40%nat) + 384) 128).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV71l HV71r] G1 G2 G8 G9 G22 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 K20 [K21l K21r] [K22l K22r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 71%nat => (V 71%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 72%nat. }
  assert (HR: regs_ok E Pv5H3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5H3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5H3.kn0).
  { unfold know_ok, Pv5H3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18; nodj) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K22l K22r; nodj) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K21l K21r; nodj) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K22l K22r; nodj) | exact (conj K22l K22r)]. }
    apply Forall_nil. }
  destruct (Pv5H3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5H3.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 40%nat) / 8) + 2147450924) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450924) + 4) -> ~ (((V 40%nat) + 352) <= bv_unsigned a < ((V 40%nat) + 352) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pv5H3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5H3.ps0) with 0x8f690 in Hms. change (SR.ps_regs Pv5H3.ps0) with (map (fun i => (i, nth i Pv5H3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5H3.ps0) with Pv5H3.cells0 in Hcells. unfold Pv5H3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5H3.regs0 Pv5H3.regs_out0 80 KS_v5H3 KS_v5H3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5H3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5H3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5H3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5H3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5H3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5H3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5H3.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth Pv5H3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk' ZA Hag ltac:(clear - HV71l HV71r K21l K21r; nodj) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5H4i := LibSegZ_v5H4i.
Definition KS_v5H4i : list nat := Eval vm_compute in (BG.kept_list 80 Pv5H4i.regs0 Pv5H4i.regs_out0).
Lemma KS_v5H4i_ok : BG.kept_ok 80 Pv5H4i.regs0 Pv5H4i.regs_out0 KS_v5H4i = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5H4i_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 20) = Z_to_bv 64 (((V 35%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 352) -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487584 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 352) + 352 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 352)) -> (((V 2%nat) - 352) + 352 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 352)) -> L5.u8_at RSEGS M ((V 40%nat) + 352) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = false -> 4096 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 35%nat) 32 -> (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) ->
  ((V 35%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 35%nat)) -> ((V 35%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 35%nat)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 35%nat) / 8) + 2147450880)) ->
  ((((V 35%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 352) \/ ((V 2%nat) - 352) + 352 <= (((V 35%nat) / 8) + 2147450880)) -> 4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 32 <= 2147446784) ->
  L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 36%nat) 32 -> (((V 2%nat) - 352) + 352 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 352)) -> ((V 36%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 36%nat)) ->
  ((V 36%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 36%nat) / 8) + 2147450880)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 36%nat) / 8) + 2147450880)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 352) \/ ((V 2%nat) - 352) + 352 <= (((V 36%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 272) ((V 40%nat) + 96) -> L5.u64_at RSEGS M ((V 2%nat) - 248) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 312) (V 57%nat) -> 0 <= (V 57%nat) <= 1 ->
  L5.u64_at RSEGS M ((V 2%nat) - 240) (((V 40%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 256) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 264) ((V 40%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 288) (V 59%nat) ->
  0 <= (V 59%nat) <= 2 -> L5.u64_at RSEGS M ((V 2%nat) - 280) (V 40%nat) -> L5.u8_at RSEGS M (V 35%nat) (V 69%nat) -> 0 <= (V 69%nat) <= 255 ->
  L5.u8_at RSEGS M (V 36%nat) (V 72%nat) -> 0 <= (V 72%nat) <= 255 -> ((V 35%nat) + 32 <= (V 36%nat) \/ (V 36%nat) + 32 <= (V 35%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 40%nat) / 8) + 2147450924) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450924) + 4) -> ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 40%nat) / 8) + 2147450924) <= i < (((V 40%nat) / 8) + 2147450924) + 4) -> ~ (((V 35%nat) + 0) <= i < ((V 35%nat) + 0) + 1) -> ~ (((V 36%nat) + 0) <= i < ((V 36%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x92ba8 M) (st fx' R' 0x92c3c M')
        /\ (forall x, In x KS_v5H4i -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ bv_unsigned (getr R' (reg 11)) = (Z.lor (Z.land (V 72%nat) 253) (V 59%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 40%nat) + 32)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 40%nat) + 96)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 40%nat)
        /\ L5.u8_at RSEGS M' (V 36%nat) (Z.lor (Z.land (V 72%nat) 253) (V 59%nat))
        /\ L5.u8_at RSEGS M' (V 35%nat) (Z.lor (Z.land (V 69%nat) 253) ((2 * (V 57%nat)) mod 2 ^ 64))
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450927) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450926) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450925) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450924) 248).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV36l HV36r] [HV40l HV40r] [HV41l HV41r] [HV57l HV57r] [HV58l HV58r] [HV59l HV59r] [HV60l HV60r] [HV69l HV69r] [HV72l HV72r] G1 G2 G8 G9 G20 G23 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] K21 [K22l K22r] K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 [K33l K33r] K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 [K47l K47r] K48 K49 K50 K51 [K52l K52r] K53 K54 [K55l K55r] K56 [K57l K57r] K58.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 72%nat => Z_to_bv 64 (V 72%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 57%nat => (V 57%nat) | 58%nat => (V 58%nat) | 59%nat => (V 59%nat) | 60%nat => (V 60%nat) | 69%nat => (V 69%nat) | 72%nat => (V 72%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E Pv5H4i.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5H4i.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5H4i.kn0).
  { unfold know_ok, Pv5H4i.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; lia | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21; nodj) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21; nodj) | clear; lia | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; lia | clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; lia | clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; lia | clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; lia | clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; lia | clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; lia | clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; lia | clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; lia | clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear) | generalize K41; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | evalEk ZA ltac:(clear - HV57l HV57r K47l K47r; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K47l K47r; nodj) | exact (conj K47l K47r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | evalEk ZA ltac:(clear - HV59l HV59r K52l K52r; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV59l HV59r K52l K52r; nodj) | exact (conj K52l K52r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; nodj) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | clear - HV2l HV2r K0l K0r K17 K18 K27 K32 K38 K43; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | evalEk ZA ltac:(clear - HV69l HV69r K55l K55r; nodj) | clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; lia | clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; lia | byte_tac ltac:(clear - HV69l HV69r K55l K55r) | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K55l K55r; nodj) | exact (conj K55l K55r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | evalEk ZA ltac:(clear - HV72l HV72r K57l K57r; nodj) | clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; lia | clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; lia | byte_tac ltac:(clear - HV72l HV72r K57l K57r) | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K57l K57r; nodj) | exact (conj K57l K57r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | evalEk ZA ltac:(clear) | generalize K58; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (Pv5H4i.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5H4i.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 40%nat) / 8) + 2147450924) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450924) + 4) -> ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold Pv5H4i.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5H4i.ps0) with 0x92c3c in Hms. change (SR.ps_regs Pv5H4i.ps0) with (map (fun i => (i, nth i Pv5H4i.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5H4i.ps0) with Pv5H4i.cells0 in Hcells. unfold Pv5H4i.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5H4i.regs0 Pv5H4i.regs_out0 80 KS_v5H4i KS_v5H4i_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5H4i.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5H4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5H4i.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5H4i.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg Pv5H4i.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5H4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5H4i.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth Pv5H4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5H4i.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5H4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5H4i.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pv5H4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5H4i.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pv5H4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5H4i.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pv5H4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5H4i.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5H4i.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K33l K33r K35 K38 K39 K40 K41 K42 K43 K58; nodj) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV59l HV59r K52l K52r HV72l HV72r K57l K57r) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K22l K22r K24 K27 K28 K29 K30 K31 K32 K58; nodj) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV57l HV57r K47l K47r HV69l HV69r K55l K55r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K28 K29 K30 K31 K39 K40 K41 K42; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. 
Qed.
(* [comment removed for export] *)

End L5ADIVPH.
