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
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA .
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegY_v5G5Lm LibSegY_v5G5Ll.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5ADIVPG3.
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
Module Pv5G5Lm := LibSegY_v5G5Lm.
Definition KS_v5G5Lm : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G5Lm.regs0 Pv5G5Lm.regs_out0).
Lemma KS_v5G5Lm_ok : BG.kept_ok 96 Pv5G5Lm.regs0 Pv5G5Lm.regs_out0 KS_v5G5Lm = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G5Lm_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 19) = Z_to_bv 64 (V 79%nat) -> getr R (reg 21) = Z_to_bv 64 18446744073709551615 -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487632 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 400) 400 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 68%nat) <= 140737488355328 -> aligned (V 68%nat) 8 ->
  4104 <= ((V 68%nat) + (8 * (V 69%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 68%nat) \/ (V 68%nat) + (8 * (V 69%nat)) <= 2147446784) -> 1 <= (V 69%nat) <= 134217728 -> L5KA.zeros_at M (((V 68%nat) / 8) + 2147450880) (V 69%nat) ->
  ((V 68%nat) + (8 * (V 69%nat)) <= (((V 68%nat) / 8) + 2147450880) \/ (((V 68%nat) / 8) + 2147450880) + (V 69%nat) <= (V 68%nat)) -> (((V 2%nat) - 400) + 400 <= (V 68%nat) \/ (V 68%nat) + (8 * (V 69%nat)) <= ((V 2%nat) - 400)) -> (((V 2%nat) - 400) + 400 <= (((V 68%nat) / 8) + 2147450880) \/ (((V 68%nat) / 8) + 2147450880) + (V 69%nat) <= ((V 2%nat) - 400)) -> L5.writable RSEGS M (V 68%nat) (8 * (V 69%nat)) ->
  (65536 + 6438912 <= (V 68%nat) \/ (V 68%nat) + (8 * (V 69%nat)) <= 65536) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 68%nat) -> L5KA.zeros_at M ((((V 2%nat) - 136) / 8) + 2147450880) 1 -> 1 <= (V 79%nat) <= 134217727 ->
  1 <= ((V 69%nat) - (V 79%nat)) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 68%nat) + (8 * (V 79%nat))) + 0) <= bv_unsigned a < (((V 68%nat) + (8 * (V 79%nat))) + 0) + 8) -> ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 68%nat) + (8 * (V 79%nat))) + 0) <= i < (((V 68%nat) + (8 * (V 79%nat))) + 0) + 8) -> ~ (((V 2%nat) - 392) <= i < ((V 2%nat) - 392) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x9319c M) (st fx' R' 0x9319c M')
        /\ (forall x, In x KS_v5G5Lm -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602536
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 68%nat) + (8 * (V 79%nat)))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 79%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 68%nat) + (8 * (V 79%nat))) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 392) 602536).
Proof.
  intros [HV2l HV2r] [HV58l HV58r] [HV68l HV68r] [HV69l HV69r] [HV79l HV79r] G1 G2 G8 G9 G19 G21 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] K9 [K10l K10r] K11 K12 K13 K14 K15 K16 K17 K18 [K19l K19r] [K20l K20r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 58%nat => (V 58%nat) | 68%nat => (V 68%nat) | 69%nat => (V 69%nat) | 79%nat => (V 79%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 80%nat. }
  assert (HR: regs_ok E Pv5G5Lm.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G5Lm.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G5Lm.kn0).
  { unfold know_ok, Pv5G5Lm.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K20l K20r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K20l K20r) | generalize K9; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K20l K20r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K20l K20r) | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K20l K20r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K20l K20r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K20l K20r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K20l K20r) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K20l K20r) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K20l K20r) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K20l K20r) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K20l K20r) | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K20l K20r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K20l K20r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K20l K20r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K20l K20r) | generalize K16; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K19l K19r K20l K20r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K20l K20r HV79l HV79r K19l K19r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  destruct (Pv5G5Lm.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G5Lm.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 68%nat) + (8 * (V 79%nat))) + 0) <= bv_unsigned a < (((V 68%nat) + (8 * (V 79%nat))) + 0) + 8) -> ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pv5G5Lm.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV79l HV79r K19l K19r K20l K20r) | evalEk' ZA Hag ltac:(clear) | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV79l HV79r K19l K19r K20l K20r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G5Lm.ps0) with 0x9319c in Hms. change (SR.ps_regs Pv5G5Lm.ps0) with (map (fun i => (i, nth i Pv5G5Lm.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G5Lm.ps0) with Pv5G5Lm.cells0 in Hcells. unfold Pv5G5Lm.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G5Lm.regs0 Pv5G5Lm.regs_out0 96 KS_v5G5Lm KS_v5G5Lm_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G5Lm.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G5Lm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5Lm.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G5Lm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5Lm.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G5Lm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5Lm.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5G5Lm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5Lm.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5G5Lm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5Lm.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pv5G5Lm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5Lm.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5G5Lm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV79l HV79r K19l K19r K20l K20r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G5Ll := LibSegY_v5G5Ll.
Definition KS_v5G5Ll : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G5Ll.regs0 Pv5G5Ll.regs_out0).
Lemma KS_v5G5Ll_ok : BG.kept_ok 96 Pv5G5Ll.regs0 Pv5G5Ll.regs_out0 KS_v5G5Ll = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G5Ll_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 19) = Z_to_bv 64 0 -> getr R (reg 21) = Z_to_bv 64 18446744073709551615 -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487632 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 400) 400 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 68%nat) <= 140737488355328 -> aligned (V 68%nat) 8 ->
  4104 <= ((V 68%nat) + (8 * (V 69%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 68%nat) \/ (V 68%nat) + (8 * (V 69%nat)) <= 2147446784) -> 1 <= (V 69%nat) <= 134217728 -> L5KA.zeros_at M (((V 68%nat) / 8) + 2147450880) (V 69%nat) ->
  ((V 68%nat) + (8 * (V 69%nat)) <= (((V 68%nat) / 8) + 2147450880) \/ (((V 68%nat) / 8) + 2147450880) + (V 69%nat) <= (V 68%nat)) -> (((V 2%nat) - 400) + 400 <= (V 68%nat) \/ (V 68%nat) + (8 * (V 69%nat)) <= ((V 2%nat) - 400)) -> (((V 2%nat) - 400) + 400 <= (((V 68%nat) / 8) + 2147450880) \/ (((V 68%nat) / 8) + 2147450880) + (V 69%nat) <= ((V 2%nat) - 400)) -> L5.writable RSEGS M (V 68%nat) (8 * (V 69%nat)) ->
  (65536 + 6438912 <= (V 68%nat) \/ (V 68%nat) + (8 * (V 69%nat)) <= 65536) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 68%nat) -> L5KA.zeros_at M ((((V 2%nat) - 136) / 8) + 2147450880) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 68%nat) + 0) <= bv_unsigned a < ((V 68%nat) + 0) + 8) -> ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 68%nat) + 0) <= i < ((V 68%nat) + 0) + 8) -> ~ (((V 2%nat) - 392) <= i < ((V 2%nat) - 392) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x9319c M) (st fx' R' 0x931c4 M')
        /\ (forall x, In x KS_v5G5Ll -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602536
        /\ getr R' (reg 10) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 18446744073709551615
        /\ L5.u64_at RSEGS M' (V 68%nat) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 392) 602536).
Proof.
  intros [HV2l HV2r] [HV58l HV58r] [HV68l HV68r] [HV69l HV69r] G1 G2 G8 G9 G19 G21 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] K9 [K10l K10r] K11 K12 K13 K14 K15 K16 K17 K18.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 58%nat => (V 58%nat) | 68%nat => (V 68%nat) | 69%nat => (V 69%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 70%nat. }
  assert (HR: regs_ok E Pv5G5Ll.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G5Ll.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G5Ll.kn0).
  { unfold know_ok, Pv5G5Ll.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16) | generalize K9; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16) | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16) | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16) | generalize K16; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K18]. }
    apply Forall_nil. }
  destruct (Pv5G5Ll.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G5Ll.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 68%nat) + 0) <= bv_unsigned a < ((V 68%nat) + 0) + 8) -> ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pv5G5Ll.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G5Ll.ps0) with 0x931c4 in Hms. change (SR.ps_regs Pv5G5Ll.ps0) with (map (fun i => (i, nth i Pv5G5Ll.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G5Ll.ps0) with Pv5G5Ll.cells0 in Hcells. unfold Pv5G5Ll.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G5Ll.regs0 Pv5G5Ll.regs_out0 96 KS_v5G5Ll KS_v5G5Ll_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G5Ll.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G5Ll.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5Ll.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G5Ll.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5Ll.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G5Ll.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5Ll.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5G5Ll.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5Ll.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5G5Ll.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5Ll.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pv5G5Ll.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G5Ll.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5G5Ll.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End L5ADIVPG3.
