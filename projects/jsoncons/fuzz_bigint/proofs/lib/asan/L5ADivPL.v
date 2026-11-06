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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegZ_v5HLa LibSegZ_v5HLb.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia.
Local Ltac nodj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac nodisj := L5FastLia.prune_arith; repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac lia := first [ solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ] | solve [ nodisj; L5FastLia.lia_st ] | L5FastLia.plia ].   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5ADIVPL.
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
Module Pv5HLa := LibSegZ_v5HLa.
Definition KS_v5HLa : list nat := Eval vm_compute in (BG.kept_list 80 Pv5HLa.regs0 Pv5HLa.regs_out0).
Lemma KS_v5HLa_ok : BG.kept_ok 80 Pv5HLa.regs0 Pv5HLa.regs_out0 KS_v5HLa = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5HLa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 10) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 11) = Z_to_bv 64 ((V 35%nat) + 24) -> getr R (reg 12) = Z_to_bv 64 ((V 35%nat) + 24) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 22) = Z_to_bv 64 0 -> getr R (reg 23) = Z_to_bv 64 (V 68%nat) -> getr R (reg 24) = Z_to_bv 64 2 -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487584 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 352) + 352 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 352)) -> (((V 2%nat) - 352) + 352 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 352)) -> 4096 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 352) + 352 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 352)) ->
  ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 33%nat) / 8) + 2147450880)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) ->
  ((((V 33%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 352) \/ ((V 2%nat) - 352) + 352 <= (((V 33%nat) / 8) + 2147450880)) -> 4096 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 32 <= 2147446784) ->
  L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 35%nat) 32 -> (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) -> ((V 35%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 35%nat)) ->
  ((V 35%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 35%nat)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 352) \/ ((V 2%nat) - 352) + 352 <= (((V 35%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 24) (V 70%nat) -> 0 <= (V 70%nat) <= 18446744073709551615 -> 0 <= (V 68%nat) <= 4294967295 -> ((V 33%nat) + 32 <= (V 35%nat) \/ (V 35%nat) + 32 <= (V 33%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 35%nat) + 24) <= bv_unsigned a < ((V 35%nat) + 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 35%nat) + 24) <= i < ((V 35%nat) + 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x92aec M) (st fx' R' 0x92aec M')
        /\ (forall x, In x KS_v5HLa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 35%nat) + 16)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 35%nat) + 16)
        /\ bv_unsigned (getr R' (reg 15)) = ((4294967296 * (if (V 68%nat) =? 0 then 2 ^ 64 - 1 else ((V 70%nat) / 4294967296) / (V 68%nat))) mod 2 ^ 64)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 24) = Z_to_bv 64 1).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV68l HV68r] [HV70l HV70r] G1 G2 G8 G9 G10 G11 G12 G21 G22 G23 G24 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 K26 K27 K28 [K29l K29r] K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 [K41l K41r] [K42l K42r] K43.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 68%nat => (V 68%nat) | 70%nat => (V 70%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 71%nat. }
  assert (HR: regs_ok E Pv5HLa.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5HLa.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5HLa.kn0).
  { unfold know_ok, Pv5HLa.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; nodj) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; nodj) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; nodj) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; nodj) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; nodj) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; nodj) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; nodj) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; nodj) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; lia | clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; lia | clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; nodj) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; lia | clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; lia | clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; nodj) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; nodj) | evalEk ZA ltac:(clear - HV70l HV70r K41l K41r; nodj) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K41l K41r; nodj) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K42l K42r; nodj) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K43; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; nodj) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (Pv5HLa.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5HLa.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 35%nat) + 24) <= bv_unsigned a < ((V 35%nat) + 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5HLa.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K43 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5HLa.ps0) with 0x92aec in Hms. change (SR.ps_regs Pv5HLa.ps0) with (map (fun i => (i, nth i Pv5HLa.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5HLa.ps0) with Pv5HLa.cells0 in Hcells. unfold Pv5HLa.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5HLa.regs0 Pv5HLa.regs_out0 80 KS_v5HLa KS_v5HLa_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5HLa.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5HLa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5HLa.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5HLa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5HLa.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5HLa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5HLa.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth Pv5HLa.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg Pv5HLa.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pv5HLa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pv5HLa.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5HLa.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5HLb := LibSegZ_v5HLb.
Definition KS_v5HLb : list nat := Eval vm_compute in (BG.kept_list 80 Pv5HLb.regs0 Pv5HLb.regs_out0).
Lemma KS_v5HLb_ok : BG.kept_ok 80 Pv5HLb.regs0 Pv5HLb.regs_out0 KS_v5HLb = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5HLb_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 352) -> getr R (reg 10) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 11) = Z_to_bv 64 ((V 35%nat) + 16) -> getr R (reg 12) = Z_to_bv 64 ((V 35%nat) + 16) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 22) = Z_to_bv 64 (V 71%nat) -> getr R (reg 23) = Z_to_bv 64 (V 68%nat) -> getr R (reg 24) = Z_to_bv 64 1 -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487584 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 352) 352 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 352) + 352 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 352)) -> (((V 2%nat) - 352) + 352 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 352)) -> 4096 <= (V 33%nat) <= 140737488355296 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 352) + 352 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 352)) ->
  ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 33%nat) / 8) + 2147450880)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 33%nat) / 8) + 2147450880)) ->
  ((((V 33%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 352) \/ ((V 2%nat) - 352) + 352 <= (((V 33%nat) / 8) + 2147450880)) -> 4096 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 32 <= 2147446784) ->
  L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 35%nat) 32 -> (((V 2%nat) - 352) + 352 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 352)) -> ((V 35%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 35%nat)) ->
  ((V 35%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 35%nat)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 352) \/ ((V 2%nat) - 352) + 352 <= (((V 35%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 248) (V 35%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 70%nat) -> 0 <= (V 70%nat) <= 18446744073709551615 -> 0 <= (V 68%nat) <= 4294967295 ->
  0 <= (V 71%nat) <= 18446744073709551615 -> ((V 33%nat) + 32 <= (V 35%nat) \/ (V 35%nat) + 32 <= (V 33%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 35%nat) + 16) <= bv_unsigned a < ((V 35%nat) + 16) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 35%nat) + 16) <= i < ((V 35%nat) + 16) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x92aec M) (st fx' R' 0x90780 M')
        /\ (forall x, In x KS_v5HLb -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 600944
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 35%nat) + 8)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 35%nat) + 8)
        /\ bv_unsigned (getr R' (reg 15)) = ((4294967296 * (if (V 68%nat) =? 0 then 2 ^ 64 - 1 else ((((4294967296 * (V 71%nat)) mod 2 ^ 64) + ((V 70%nat) / 4294967296)) mod 2 ^ 64) / (V 68%nat))) mod 2 ^ 64)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 24) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV68l HV68r] [HV70l HV70r] [HV71l HV71r] G1 G2 G8 G9 G10 G11 G12 G21 G22 G23 G24 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 K26 K27 K28 [K29l K29r] K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 [K42l K42r] [K43l K43r] [K44l K44r] K45.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 68%nat => (V 68%nat) | 70%nat => (V 70%nat) | 71%nat => (V 71%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 72%nat. }
  assert (HR: regs_ok E Pv5HLb.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5HLb.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5HLb.kn0).
  { unfold know_ok, Pv5HLb.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18; nodj) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; nodj) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; nodj) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; nodj) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; nodj) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; nodj) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; nodj) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; nodj) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; nodj) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; lia | clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; lia | clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; nodj) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; lia | clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; lia | clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; nodj) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K24 K25 K26 K27 K35 K36 K37 K38; nodj) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; nodj) | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; lia | clear - HV2l HV2r K0l K0r K17 K18 K23 K28 K34 K39; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; nodj) | evalEk ZA ltac:(clear - HV70l HV70r K42l K42r; nodj) | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; lia | clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K42l K42r; nodj) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K43l K43r; nodj) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K44l K44r; nodj) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19l K19r K21 K23 K24 K25 K26 K27 K28 K45; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; nodj) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (Pv5HLb.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5HLb.NX0 with 80%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 35%nat) + 16) <= bv_unsigned a < ((V 35%nat) + 16) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5HLb.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K29l K29r K31 K34 K35 K36 K37 K38 K39 K45 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5HLb.ps0) with 0x90780 in Hms. change (SR.ps_regs Pv5HLb.ps0) with (map (fun i => (i, nth i Pv5HLb.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5HLb.ps0) with Pv5HLb.cells0 in Hcells. unfold Pv5HLb.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5HLb.regs0 Pv5HLb.regs_out0 80 KS_v5HLb KS_v5HLb_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5HLb.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5HLb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5HLb.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5HLb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5HLb.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5HLb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5HLb.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5HLb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5HLb.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth Pv5HLb.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg Pv5HLb.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pv5HLb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pv5HLb.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5HLb.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End L5ADIVPL.
