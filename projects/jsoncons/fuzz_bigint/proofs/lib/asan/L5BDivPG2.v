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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegY_v5G9x LibSegY_v5G9l LibSegY_v5GLa LibSegY_v5GLb LibSegY_v5GLcm LibSegY_v5GLcl LibSegY_v5G11 LibSegY_v5G12u LibSegY_v5G12n LibSegY_v5G13 LibSegY_v5G14ai LibSegY_v5G14ad LibSegY_v5G14bi LibSegY_v5G14bd LibSegY_v5G14j.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5ADIVPG2.
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
Module Pv5G9x := LibSegY_v5G9x.
Definition KS_v5G9x : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G9x.regs0 Pv5G9x.regs_out0).
Lemma KS_v5G9x_ok : BG.kept_ok 96 Pv5G9x.regs0 Pv5G9x.regs_out0 KS_v5G9x = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G9x_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 19) = Z_to_bv 64 (V 73%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 74%nat) ->
  140735332487632 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 400) 400 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 65%nat) <= 140737488355328 -> aligned (V 65%nat) 8 ->
  4104 <= ((8 * (V 64%nat)) + (V 65%nat)) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 65%nat) \/ (V 65%nat) + (8 * (V 64%nat)) <= 2147446784) -> 1 <= (V 64%nat) <= 134217728 -> L5KA.zeros_at M (((V 65%nat) / 8) + 2147450880) (V 64%nat) ->
  ((V 65%nat) + (8 * (V 64%nat)) <= (((V 65%nat) / 8) + 2147450880) \/ (((V 65%nat) / 8) + 2147450880) + (V 64%nat) <= (V 65%nat)) -> (((V 2%nat) - 400) + 400 <= (V 65%nat) \/ (V 65%nat) + (8 * (V 64%nat)) <= ((V 2%nat) - 400)) -> (((V 2%nat) - 400) + 400 <= (((V 65%nat) / 8) + 2147450880) \/ (((V 65%nat) / 8) + 2147450880) + (V 64%nat) <= ((V 2%nat) - 400)) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 65%nat) ->
  L5KA.zeros_at M ((((V 2%nat) - 120) / 8) + 2147450880) 1 -> 0 <= (V 73%nat) <= 134217727 -> 0 <= (V 74%nat) <= 134217727 -> 1 <= ((V 64%nat) - (V 74%nat)) <= 134217728 ->
  0 <= (((-1) * (V 73%nat)) + (V 74%nat)) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 392) <= i < ((V 2%nat) - 392) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93350 M) (st fx' R' 0x93458 M')
        /\ (forall x, In x KS_v5G9x -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602972
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 65%nat) + (8 * (V 74%nat)))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 392) 602972).
Proof.
  intros [HV2l HV2r] [HV58l HV58r] [HV64l HV64r] [HV65l HV65r] [HV73l HV73r] [HV74l HV74r] G1 G2 G8 G9 G19 G23 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] K9 [K10l K10r] K11 K12 K13 K14 K15 K16 [K17l K17r] [K18l K18r] [K19l K19r] [K20l K20r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 58%nat => (V 58%nat) | 64%nat => (V 64%nat) | 65%nat => (V 65%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 75%nat. }
  assert (HR: regs_ok E Pv5G9x.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G9x.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G9x.kn0).
  { unfold know_ok, Pv5G9x.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r HV65l HV65r K6l K6r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r) | generalize K9; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r) | clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r HV65l HV65r K6l K6r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r HV65l HV65r K6l K6r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r HV65l HV65r K6l K6r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r) | evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K15]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K17l K17r K20l K20r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K18l K18r K19l K19r K20l K20r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r HV74l HV74r K18l K18r K20l K20r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K17l K17r K20l K20r HV74l HV74r K18l K18r K19l K19r) | exact (conj K20l K20r)]. }
    apply Forall_nil. }
  destruct (Pv5G9x.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G9x.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5G9x.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G9x.ps0) with 0x93458 in Hms. change (SR.ps_regs Pv5G9x.ps0) with (map (fun i => (i, nth i Pv5G9x.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G9x.ps0) with Pv5G9x.cells0 in Hcells. unfold Pv5G9x.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G9x.regs0 Pv5G9x.regs_out0 96 KS_v5G9x KS_v5G9x_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G9x.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G9x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G9x.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G9x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G9x.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G9x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G9x.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5G9x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G9x.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5G9x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G9x.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pv5G9x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G9l := LibSegY_v5G9l.
Definition KS_v5G9l : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G9l.regs0 Pv5G9l.regs_out0).
Lemma KS_v5G9l_ok : BG.kept_ok 96 Pv5G9l.regs0 Pv5G9l.regs_out0 KS_v5G9l = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G9l_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 19) = Z_to_bv 64 (V 73%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 27) = Z_to_bv 64 (V 74%nat) ->
  140735332487632 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 400) 400 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 65%nat) <= 140737488355328 -> aligned (V 65%nat) 8 ->
  4104 <= ((8 * (V 64%nat)) + (V 65%nat)) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 65%nat) \/ (V 65%nat) + (8 * (V 64%nat)) <= 2147446784) -> 1 <= (V 64%nat) <= 134217728 -> L5KA.zeros_at M (((V 65%nat) / 8) + 2147450880) (V 64%nat) ->
  ((V 65%nat) + (8 * (V 64%nat)) <= (((V 65%nat) / 8) + 2147450880) \/ (((V 65%nat) / 8) + 2147450880) + (V 64%nat) <= (V 65%nat)) -> (((V 2%nat) - 400) + 400 <= (V 65%nat) \/ (V 65%nat) + (8 * (V 64%nat)) <= ((V 2%nat) - 400)) -> (((V 2%nat) - 400) + 400 <= (((V 65%nat) / 8) + 2147450880) \/ (((V 65%nat) / 8) + 2147450880) + (V 64%nat) <= ((V 2%nat) - 400)) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 65%nat) ->
  L5KA.zeros_at M ((((V 2%nat) - 120) / 8) + 2147450880) 1 -> 0 <= (V 73%nat) <= 134217727 -> 0 <= (V 74%nat) <= 134217727 -> 1 <= ((V 64%nat) - (V 74%nat)) <= 134217728 ->
  1 <= ((V 73%nat) - (V 74%nat)) <= 134217728 -> L5.u64_at RSEGS M ((V 65%nat) + (8 * (V 74%nat))) (V 75%nat) -> 0 <= (V 75%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 272) ((V 74%nat) + 1) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 392) <= i < ((V 2%nat) - 392) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93350 M) (st fx' R' 0x93394 M')
        /\ (forall x, In x KS_v5G9l -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 602972
        /\ getr R' (reg 10) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 73%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((8 * (V 74%nat)) + 8)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 74%nat) + 1)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 (((-1) * (V 74%nat)) + 1152921504606846975)
        /\ getr R' (reg 24) = Z_to_bv 64 (((8 * (V 73%nat)) + ((-8) * (V 74%nat))) - 8)
        /\ getr R' (reg 25) = Z_to_bv 64 (((-1) * (V 74%nat)) - 1)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 392) 602972).
Proof.
  intros [HV2l HV2r] [HV58l HV58r] [HV64l HV64r] [HV65l HV65r] [HV73l HV73r] [HV74l HV74r] [HV75l HV75r] G1 G2 G8 G9 G19 G23 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] K9 [K10l K10r] K11 K12 K13 K14 K15 K16 [K17l K17r] [K18l K18r] [K19l K19r] [K20l K20r] K21 [K22l K22r] K23.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 64%nat => Z_to_bv 64 (V 64%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 58%nat => (V 58%nat) | 64%nat => (V 64%nat) | 65%nat => (V 65%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | 75%nat => (V 75%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E Pv5G9l.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G9l.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G9l.kn0).
  { unfold know_ok, Pv5G9l.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r HV65l HV65r K6l K6r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r) | generalize K9; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r) | clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r HV65l HV65r K6l K6r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r HV65l HV65r K6l K6r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r HV65l HV65r K6l K6r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r) | evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K15]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K17l K17r K20l K20r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K18l K18r K19l K19r K20l K20r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K8l K8r K9 K10l K10r K12 K13 K14 K19l K19r HV74l HV74r K18l K18r K20l K20r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K17l K17r K20l K20r HV74l HV74r K18l K18r K19l K19r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14 HV74l HV74r K18l K18r K19l K19r K20l K20r) | evalEk ZA ltac:(clear - HV75l HV75r K22l K22r) | clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14 HV74l HV74r K18l K18r K19l K19r K20l K20r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV65l HV65r K6l K6r K8l K8r K9 K12 K13 K14 HV74l HV74r K18l K18r K19l K19r K20l K20r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear - HV74l HV74r K18l K18r K19l K19r K20l K20r) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K23]. }
    apply Forall_nil. }
  destruct (Pv5G9l.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G9l.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5G9l.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G9l.ps0) with 0x93394 in Hms. change (SR.ps_regs Pv5G9l.ps0) with (map (fun i => (i, nth i Pv5G9l.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G9l.ps0) with Pv5G9l.cells0 in Hcells. unfold Pv5G9l.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G9l.regs0 Pv5G9l.regs_out0 96 KS_v5G9l KS_v5G9l_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G9l.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G9l.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G9l.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G9l.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G9l.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G9l.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G9l.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5G9l.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G9l.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5G9l.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G9l.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pv5G9l.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G9l.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth Pv5G9l.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G9l.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5G9l.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G9l.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pv5G9l.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G9l.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth Pv5G9l.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5GLa := LibSegY_v5GLa.
Definition KS_v5GLa : list nat := Eval vm_compute in (BG.kept_list 96 Pv5GLa.regs0 Pv5GLa.regs_out0).
Lemma KS_v5GLa_ok : BG.kept_ok 96 Pv5GLa.regs0 Pv5GLa.regs_out0 KS_v5GLa = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5GLa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 19) = Z_to_bv 64 (V 73%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 (V 75%nat) ->
  140735332487632 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 400) 400 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 70%nat) <= 140737488355328 -> aligned (V 70%nat) 8 ->
  4104 <= ((V 70%nat) + (8 * (V 71%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 70%nat) \/ (V 70%nat) + (8 * (V 71%nat)) <= 2147446784) -> 1 <= (V 71%nat) <= 134217728 -> L5KA.zeros_at M (((V 70%nat) / 8) + 2147450880) (V 71%nat) ->
  ((V 70%nat) + (8 * (V 71%nat)) <= (((V 70%nat) / 8) + 2147450880) \/ (((V 70%nat) / 8) + 2147450880) + (V 71%nat) <= (V 70%nat)) -> (((V 2%nat) - 400) + 400 <= (V 70%nat) \/ (V 70%nat) + (8 * (V 71%nat)) <= ((V 2%nat) - 400)) -> (((V 2%nat) - 400) + 400 <= (((V 70%nat) / 8) + 2147450880) \/ (((V 70%nat) / 8) + 2147450880) + (V 71%nat) <= ((V 2%nat) - 400)) -> L5.u64_at RSEGS M ((V 2%nat) - 240) (V 70%nat) ->
  L5KA.zeros_at M ((((V 2%nat) - 240) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 264) (V 33%nat) -> 0 <= (V 33%nat) <= 18446744073709551615 -> 0 <= (V 75%nat) <= 18446744073709551615 ->
  1 <= (V 73%nat) <= 134217727 -> 1 <= ((V 71%nat) - (V 73%nat)) <= 134217728 -> L5.u64_at RSEGS M (((V 70%nat) + (8 * (V 73%nat))) - 8) (V 77%nat) -> 0 <= (V 77%nat) <= 18446744073709551615 ->
  L5.u64_at RSEGS M ((V 70%nat) + (8 * (V 73%nat))) (V 76%nat) -> 0 <= (V 76%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 392) <= i < ((V 2%nat) - 392) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93394 M) (st fx' R' 0x9403c M')
        /\ (forall x, In x KS_v5GLa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 603112
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 76%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 77%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 (V 76%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 73%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 392) 603076).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV58l HV58r] [HV70l HV70r] [HV71l HV71r] [HV73l HV73r] [HV75l HV75r] [HV76l HV76r] [HV77l HV77r] G1 G2 G8 G9 G19 G23 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] K9 [K10l K10r] K11 K12 K13 K14 K15 K16 K17 [K18l K18r] [K19l K19r] [K20l K20r] [K21l K21r] K22 [K23l K23r] K24 [K25l K25r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | 71%nat => Z_to_bv 64 (V 71%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 58%nat => (V 58%nat) | 70%nat => (V 70%nat) | 71%nat => (V 71%nat) | 73%nat => (V 73%nat) | 75%nat => (V 75%nat) | 76%nat => (V 76%nat) | 77%nat => (V 77%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 78%nat. }
  assert (HR: regs_ok E Pv5GLa.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5GLa.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5GLa.kn0).
  { unfold know_ok, Pv5GLa.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14 HV71l HV71r K10l K10r K21l K21r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV71l HV71r K8l K8r K9 K10l K10r K12 K13 K14 K21l K21r) | generalize K9; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K8l K8r K9 K10l K10r K12 K13 K14 K21l K21r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV71l HV71r K8l K8r K9 K10l K10r K12 K13 K14 K21l K21r) | clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14 HV71l HV71r K10l K10r K21l K21r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14 HV71l HV71r K10l K10r K21l K21r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14 HV71l HV71r K10l K10r K21l K21r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV71l HV71r K8l K8r K9 K10l K10r K12 K13 K14 K21l K21r) | evalEk ZA ltac:(clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV71l HV71r K8l K8r K9 K10l K10r K12 K13 K14 K21l K21r) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV71l HV71r K8l K8r K9 K10l K10r K12 K13 K14 K21l K21r) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14) | evalEk ZA ltac:(clear - HV71l HV71r K8l K8r K9 K10l K10r K12 K13 K14 K21l K21r) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K15]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear - HV33l HV33r K18l K18r) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K20l K20r K21l K21r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K8l K8r K9 K10l K10r K12 K13 K14 K21l K21r HV73l HV73r K20l K20r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14 HV73l HV73r K20l K20r K21l K21r) | evalEk ZA ltac:(clear - HV77l HV77r K23l K23r) | clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14 HV73l HV73r K20l K20r K21l K21r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14 HV73l HV73r K20l K20r K21l K21r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV77l HV77r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14 HV73l HV73r K20l K20r K21l K21r) | evalEk ZA ltac:(clear - HV76l HV76r K25l K25r) | clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14 HV73l HV73r K20l K20r K21l K21r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV70l HV70r K6l K6r K8l K8r K9 K12 K13 K14 HV73l HV73r K20l K20r K21l K21r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV76l HV76r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  destruct (Pv5GLa.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5GLa.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5GLa.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5GLa.ps0) with 0x9403c in Hms. change (SR.ps_regs Pv5GLa.ps0) with (map (fun i => (i, nth i Pv5GLa.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5GLa.ps0) with Pv5GLa.cells0 in Hcells. unfold Pv5GLa.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5GLa.regs0 Pv5GLa.regs_out0 96 KS_v5GLa KS_v5GLa_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5GLa.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5GLa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLa.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5GLa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLa.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5GLa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLa.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5GLa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLa.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5GLa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLa.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pv5GLa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLa.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pv5GLa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLa.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pv5GLa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5GLb := LibSegY_v5GLb.
Definition KS_v5GLb : list nat := Eval vm_compute in (BG.kept_list 96 Pv5GLb.regs0 Pv5GLb.regs_out0).
Lemma KS_v5GLb_ok : BG.kept_ok 96 Pv5GLb.regs0 Pv5GLb.regs_out0 KS_v5GLb = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5GLb_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 80%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 10) = Z_to_bv 64 (V 78%nat) -> getr R (reg 19) = Z_to_bv 64 (V 73%nat) -> getr R (reg 21) = Z_to_bv 64 (((-1) * (V 74%nat)) + 1152921504606846975) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 (8 * (V 80%nat)) -> getr R (reg 25) = Z_to_bv 64 (((-1) * (V 74%nat)) - 1) ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 0 <= (V 78%nat) <= 18446744073709551615 -> 1 <= (V 73%nat) <= 134217727 ->
  0 <= (V 74%nat) <= 134217727 -> 0 <= (V 80%nat) <= 134217727 -> L5.u64_at RSEGS M ((V 2%nat) - 240) (V 70%nat) -> 4096 <= (V 70%nat) <= 140737488355328 ->
  aligned (V 70%nat) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 65%nat) -> 0 <= (V 65%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 272) ((V 74%nat) + 1) ->
  L5.u64_at RSEGS M ((V 2%nat) - 264) (V 33%nat) -> 0 <= (V 33%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 248) <= bv_unsigned a < ((V 2%nat) - 248) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 248) <= i < ((V 2%nat) - 248) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x933e8 M) (st fx' R' 0x9413c M')
        /\ (forall x, In x KS_v5GLb -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 603176
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 70%nat) + (8 * (V 80%nat)))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 74%nat) + 1)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 248)
        /\ getr R' (reg 19) = Z_to_bv 64 (((V 73%nat) - (V 74%nat)) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 248) (V 78%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV58l HV58r] [HV65l HV65r] [HV70l HV70r] [HV73l HV73r] [HV74l HV74r] [HV78l HV78r] [HV80l HV80r] G1 G2 G8 G9 G10 G19 G21 G23 G24 G25 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] [K7l K7r] [K8l K8r] [K9l K9r] K10 [K11l K11r] K12 K13 [K14l K14r] K15 K16 [K17l K17r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 65%nat => Z_to_bv 64 (V 65%nat) | 70%nat => Z_to_bv 64 (V 70%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 78%nat => Z_to_bv 64 (V 78%nat) | 80%nat => Z_to_bv 64 (V 80%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 58%nat => (V 58%nat) | 65%nat => (V 65%nat) | 70%nat => (V 70%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | 78%nat => (V 78%nat) | 80%nat => (V 80%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 81%nat. }
  assert (HR: regs_ok E Pv5GLb.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5GLb.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5GLb.kn0).
  { unfold know_ok, Pv5GLb.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV78l HV78r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV80l HV80r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV70l HV70r K11l K11r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV70l HV70r K11l K11r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV65l HV65r K14l K14r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV74l HV74r K8l K8r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV33l HV33r K17l K17r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  destruct (Pv5GLb.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5GLb.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 248) <= bv_unsigned a < ((V 2%nat) - 248) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5GLb.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5GLb.ps0) with 0x9413c in Hms. change (SR.ps_regs Pv5GLb.ps0) with (map (fun i => (i, nth i Pv5GLb.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5GLb.ps0) with Pv5GLb.cells0 in Hcells. unfold Pv5GLb.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5GLb.regs0 Pv5GLb.regs_out0 96 KS_v5GLb KS_v5GLb_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5GLb.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5GLb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLb.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5GLb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLb.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5GLb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLb.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5GLb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLb.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5GLb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLb.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pv5GLb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLb.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5GLb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV78l HV78r K6l K6r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5GLcm := LibSegY_v5GLcm.
Definition KS_v5GLcm : list nat := Eval vm_compute in (BG.kept_list 96 Pv5GLcm.regs0 Pv5GLcm.regs_out0).
Lemma KS_v5GLcm_ok : BG.kept_ok 96 Pv5GLcm.regs0 Pv5GLcm.regs_out0 KS_v5GLcm = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5GLcm_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 80%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 19) = Z_to_bv 64 (V 80%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 73%nat) - 1) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 (8 * (V 80%nat)) -> getr R (reg 27) = Z_to_bv 64 (V 74%nat) ->
  140735332487632 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 400) 400 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 68%nat) <= 140737488355328 -> aligned (V 68%nat) 8 ->
  4104 <= ((V 68%nat) + (8 * (V 69%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 68%nat) \/ (V 68%nat) + (8 * (V 69%nat)) <= 2147446784) -> 1 <= (V 69%nat) <= 134217728 -> L5KA.zeros_at M (((V 68%nat) / 8) + 2147450880) (V 69%nat) ->
  ((V 68%nat) + (8 * (V 69%nat)) <= (((V 68%nat) / 8) + 2147450880) \/ (((V 68%nat) / 8) + 2147450880) + (V 69%nat) <= (V 68%nat)) -> (((V 2%nat) - 400) + 400 <= (V 68%nat) \/ (V 68%nat) + (8 * (V 69%nat)) <= ((V 2%nat) - 400)) -> (((V 2%nat) - 400) + 400 <= (((V 68%nat) / 8) + 2147450880) \/ (((V 68%nat) / 8) + 2147450880) + (V 69%nat) <= ((V 2%nat) - 400)) -> L5.writable RSEGS M (V 68%nat) (8 * (V 69%nat)) ->
  (65536 + 6438912 <= (V 68%nat) \/ (V 68%nat) + (8 * (V 69%nat)) <= 65536) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 68%nat) -> L5KA.zeros_at M ((((V 2%nat) - 136) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 248) (V 78%nat) ->
  0 <= (V 78%nat) <= 18446744073709551615 -> 0 <= (V 80%nat) <= 134217727 -> 1 <= ((V 69%nat) - (V 80%nat)) <= 134217728 -> 1 <= (V 73%nat) <= 134217727 ->
  0 <= (V 74%nat) <= 134217727 -> 2 <= ((V 73%nat) - (V 74%nat)) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 68%nat) + (8 * (V 80%nat))) + 0) <= bv_unsigned a < (((V 68%nat) + (8 * (V 80%nat))) + 0) + 8) -> ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 68%nat) + (8 * (V 80%nat))) + 0) <= i < (((V 68%nat) + (8 * (V 80%nat))) + 0) + 8) -> ~ (((V 2%nat) - 392) <= i < ((V 2%nat) - 392) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93428 M) (st fx' R' 0x93394 M')
        /\ (forall x, In x KS_v5GLcm -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 603192
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 68%nat) + (8 * (V 80%nat)))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 73%nat) - 1)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 78%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 ((8 * (V 80%nat)) - 8)
        /\ L5.u64_at RSEGS M' ((V 68%nat) + (8 * (V 80%nat))) (V 78%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 392) 603192).
Proof.
  intros [HV2l HV2r] [HV58l HV58r] [HV68l HV68r] [HV69l HV69r] [HV73l HV73r] [HV74l HV74r] [HV78l HV78r] [HV80l HV80r] G1 G2 G8 G9 G19 G22 G23 G24 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] K9 [K10l K10r] K11 K12 K13 K14 K15 K16 K17 K18 K19 [K20l K20r] [K21l K21r] [K22l K22r] [K23l K23r] [K24l K24r] [K25l K25r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 78%nat => Z_to_bv 64 (V 78%nat) | 80%nat => Z_to_bv 64 (V 80%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 58%nat => (V 58%nat) | 68%nat => (V 68%nat) | 69%nat => (V 69%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | 78%nat => (V 78%nat) | 80%nat => (V 80%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 81%nat. }
  assert (HR: regs_ok E Pv5GLcm.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5GLcm.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5GLcm.kn0).
  { unfold know_ok, Pv5GLcm.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K22l K22r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | generalize K9; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K22l K22r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K22l K22r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K22l K22r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K22l K22r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K22l K22r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K22l K22r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | generalize K16; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear - HV78l HV78r K20l K20r) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV78l HV78r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV80l HV80r K21l K21r K22l K22r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r HV80l HV80r K21l K21r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K23l K23r K25l K25r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K24l K24r K25l K25r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K23l K23r K25l K25r HV74l HV74r K24l K24r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  destruct (Pv5GLcm.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5GLcm.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 68%nat) + (8 * (V 80%nat))) + 0) <= bv_unsigned a < (((V 68%nat) + (8 * (V 80%nat))) + 0) + 8) -> ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pv5GLcm.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV80l HV80r K21l K21r K22l K22r) | evalEk' ZA Hag ltac:(clear) | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV80l HV80r K21l K21r K22l K22r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5GLcm.ps0) with 0x93394 in Hms. change (SR.ps_regs Pv5GLcm.ps0) with (map (fun i => (i, nth i Pv5GLcm.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5GLcm.ps0) with Pv5GLcm.cells0 in Hcells. unfold Pv5GLcm.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5GLcm.regs0 Pv5GLcm.regs_out0 96 KS_v5GLcm KS_v5GLcm_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5GLcm.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5GLcm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcm.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5GLcm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcm.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5GLcm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcm.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5GLcm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcm.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5GLcm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcm.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pv5GLcm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcm.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5GLcm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcm.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pv5GLcm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcm.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5GLcm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV80l HV80r K21l K21r K22l K22r) | evalEk' ZA Hag ltac:(clear - HV78l HV78r K20l K20r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5GLcl := LibSegY_v5GLcl.
Definition KS_v5GLcl : list nat := Eval vm_compute in (BG.kept_list 96 Pv5GLcl.regs0 Pv5GLcl.regs_out0).
Lemma KS_v5GLcl_ok : BG.kept_ok 96 Pv5GLcl.regs0 Pv5GLcl.regs_out0 KS_v5GLcl = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5GLcl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 80%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 19) = Z_to_bv 64 (V 80%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 73%nat) - 1) -> getr R (reg 23) = Z_to_bv 64 2147450880 -> getr R (reg 24) = Z_to_bv 64 (8 * (V 80%nat)) -> getr R (reg 27) = Z_to_bv 64 (V 74%nat) ->
  140735332487632 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 400) 400 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 68%nat) <= 140737488355328 -> aligned (V 68%nat) 8 ->
  4104 <= ((V 68%nat) + (8 * (V 69%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 68%nat) \/ (V 68%nat) + (8 * (V 69%nat)) <= 2147446784) -> 1 <= (V 69%nat) <= 134217728 -> L5KA.zeros_at M (((V 68%nat) / 8) + 2147450880) (V 69%nat) ->
  ((V 68%nat) + (8 * (V 69%nat)) <= (((V 68%nat) / 8) + 2147450880) \/ (((V 68%nat) / 8) + 2147450880) + (V 69%nat) <= (V 68%nat)) -> (((V 2%nat) - 400) + 400 <= (V 68%nat) \/ (V 68%nat) + (8 * (V 69%nat)) <= ((V 2%nat) - 400)) -> (((V 2%nat) - 400) + 400 <= (((V 68%nat) / 8) + 2147450880) \/ (((V 68%nat) / 8) + 2147450880) + (V 69%nat) <= ((V 2%nat) - 400)) -> L5.writable RSEGS M (V 68%nat) (8 * (V 69%nat)) ->
  (65536 + 6438912 <= (V 68%nat) \/ (V 68%nat) + (8 * (V 69%nat)) <= 65536) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 68%nat) -> L5KA.zeros_at M ((((V 2%nat) - 136) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 248) (V 78%nat) ->
  0 <= (V 78%nat) <= 18446744073709551615 -> 0 <= (V 80%nat) <= 134217727 -> 1 <= ((V 69%nat) - (V 80%nat)) <= 134217728 -> 1 <= (V 73%nat) <= 134217727 ->
  0 <= (V 74%nat) <= 134217727 -> 1 <= ((V 73%nat) - (V 74%nat)) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 68%nat) + (8 * (V 80%nat))) + 0) <= bv_unsigned a < (((V 68%nat) + (8 * (V 80%nat))) + 0) + 8) -> ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 68%nat) + (8 * (V 80%nat))) + 0) <= i < (((V 68%nat) + (8 * (V 80%nat))) + 0) + 8) -> ~ (((V 2%nat) - 392) <= i < ((V 2%nat) - 392) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93428 M) (st fx' R' 0x93458 M')
        /\ (forall x, In x KS_v5GLcl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 603192
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 68%nat) + (8 * (V 80%nat)))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 73%nat) - 1)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 78%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 ((8 * (V 80%nat)) - 8)
        /\ L5.u64_at RSEGS M' ((V 68%nat) + (8 * (V 80%nat))) (V 78%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 392) 603192).
Proof.
  intros [HV2l HV2r] [HV58l HV58r] [HV68l HV68r] [HV69l HV69r] [HV73l HV73r] [HV74l HV74r] [HV78l HV78r] [HV80l HV80r] G1 G2 G8 G9 G19 G22 G23 G24 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 [K8l K8r] K9 [K10l K10r] K11 K12 K13 K14 K15 K16 K17 K18 K19 [K20l K20r] [K21l K21r] [K22l K22r] [K23l K23r] [K24l K24r] [K25l K25r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 68%nat => Z_to_bv 64 (V 68%nat) | 69%nat => Z_to_bv 64 (V 69%nat) | 73%nat => Z_to_bv 64 (V 73%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 78%nat => Z_to_bv 64 (V 78%nat) | 80%nat => Z_to_bv 64 (V 80%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 58%nat => (V 58%nat) | 68%nat => (V 68%nat) | 69%nat => (V 69%nat) | 73%nat => (V 73%nat) | 74%nat => (V 74%nat) | 78%nat => (V 78%nat) | 80%nat => (V 80%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 81%nat. }
  assert (HR: regs_ok E Pv5GLcl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5GLcl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5GLcl.kn0).
  { unfold know_ok, Pv5GLcl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K22l K22r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | generalize K9; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K22l K22r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K22l K22r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K22l K22r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K22l K22r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K22l K22r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV69l HV69r K10l K10r K22l K22r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r) | generalize K16; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk ZA ltac:(clear - HV78l HV78r K20l K20r) | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K13 K14; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV78l HV78r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV80l HV80r K21l K21r K22l K22r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K8l K8r K9 K10l K10r K12 K13 K14 K16 K22l K22r HV80l HV80r K21l K21r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K23l K23r K25l K25r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K24l K24r K25l K25r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K23l K23r K25l K25r HV74l HV74r K24l K24r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  destruct (Pv5GLcl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5GLcl.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 68%nat) + (8 * (V 80%nat))) + 0) <= bv_unsigned a < (((V 68%nat) + (8 * (V 80%nat))) + 0) + 8) -> ~ (((V 2%nat) - 392) <= bv_unsigned a < ((V 2%nat) - 392) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold Pv5GLcl.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV80l HV80r K21l K21r K22l K22r) | evalEk' ZA Hag ltac:(clear) | clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV80l HV80r K21l K21r K22l K22r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K14 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5GLcl.ps0) with 0x93458 in Hms. change (SR.ps_regs Pv5GLcl.ps0) with (map (fun i => (i, nth i Pv5GLcl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5GLcl.ps0) with Pv5GLcl.cells0 in Hcells. unfold Pv5GLcl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5GLcl.regs0 Pv5GLcl.regs_out0 96 KS_v5GLcl KS_v5GLcl_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5GLcl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5GLcl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5GLcl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcl.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5GLcl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcl.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5GLcl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcl.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5GLcl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcl.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pv5GLcl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcl.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5GLcl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcl.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pv5GLcl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5GLcl.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5GLcl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV68l HV68r K6l K6r K8l K8r K9 K12 K13 K14 K16 HV80l HV80r K21l K21r K22l K22r) | evalEk' ZA Hag ltac:(clear - HV78l HV78r K20l K20r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G11 := LibSegY_v5G11.
Definition KS_v5G11 : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G11.regs0 Pv5G11.regs_out0).
Lemma KS_v5G11_ok : BG.kept_ok 96 Pv5G11.regs0 Pv5G11.regs_out0 KS_v5G11 = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G11_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 296) (V 35%nat) -> 0 <= (V 35%nat) <= 18446744073709551615 ->
  L5.u64_at RSEGS M ((V 2%nat) - 360) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 336) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 304) ((V 40%nat) + 32) -> L5.u64_at RSEGS M ((V 2%nat) - 280) ((V 40%nat) + 96) ->
  4096 <= (V 40%nat) <= 140737488354816 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93458 M) (st fx' R' 0x90d58 M')
        /\ (forall x, In x KS_v5G11 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 603252
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 40%nat) + 32)
        /\ getr R' (reg 25) = Z_to_bv 64 ((V 40%nat) + 96)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 40%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV40l HV40r] [HV58l HV58r] G1 G2 G8 G9 G23 [K0l K0r] K1 K2 K3 K4 K5 K6 [K7l K7r] K8 K9 K10 K11 [K12l K12r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E Pv5G11.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G11.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G11.kn0).
  { unfold know_ok, Pv5G11.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV35l HV35r K7l K7r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV40l HV40r K12l K12r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV40l HV40r K12l K12r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV40l HV40r K12l K12r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV40l HV40r K12l K12r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  destruct (Pv5G11.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G11.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pv5G11.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G11.ps0) with 0x90d58 in Hms. change (SR.ps_regs Pv5G11.ps0) with (map (fun i => (i, nth i Pv5G11.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G11.ps0) with Pv5G11.cells0 in Hcells. unfold Pv5G11.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G11.regs0 Pv5G11.regs_out0 96 KS_v5G11 KS_v5G11_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G11.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G11.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G11.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth Pv5G11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G11.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth Pv5G11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G11.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth Pv5G11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G11.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth Pv5G11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pv5G11.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth Pv5G11.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G12u := LibSegY_v5G12u.
Definition KS_v5G12u : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G12u.regs0 Pv5G12u.regs_out0).
Lemma KS_v5G12u_ok : BG.kept_ok 96 Pv5G12u.regs0 Pv5G12u.regs_out0 KS_v5G12u = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G12u_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 88%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 35%nat) 32 -> (((V 2%nat) - 384) + 384 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 384)) ->
  ((V 35%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 35%nat)) -> ((V 35%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 35%nat)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 35%nat) / 8) + 2147450880)) ->
  ((((V 35%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 384) \/ ((V 2%nat) - 384) + 384 <= (((V 35%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 288) (V 36%nat) -> 0 <= (V 36%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 320) (((V 35%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 264) (V 33%nat) -> 0 <= (V 33%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 312) (V 57%nat) -> 0 <= (V 57%nat) <= 1 ->
  L5.u64_at RSEGS M ((V 2%nat) - 344) (V 37%nat) -> 1 <= (V 37%nat) <= 1 -> L5.u8_at RSEGS M (V 35%nat) (V 60%nat) -> 0 <= (V 60%nat) <= 255 ->
  L5.u32_at RSEGS M ((V 2%nat) - 220) (V 88%nat) -> 0 <= (V 88%nat) <= 63 -> L5.u64_at RSEGS M ((V 2%nat) - 376) (V 63%nat) -> 0 <= (V 63%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 35%nat) + 0) <= i < ((V 35%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93474 M) (st fx' R' 0x943f8 M')
        /\ (forall x, In x KS_v5G12u -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 603324
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 88%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ L5.u8_at RSEGS M' (V 35%nat) (Z.lor (Z.land (V 60%nat) 253) ((2 * (V 57%nat)) mod 2 ^ 64))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV40l HV40r] [HV57l HV57r] [HV58l HV58r] [HV60l HV60r] [HV63l HV63r] [HV88l HV88r] G1 G2 G8 G9 G20 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 [K18l K18r] K19 K20 [K21l K21r] K22 [K23l K23r] K24 [K25l K25r] K26 [K27l K27r] K28 [K29l K29r] K30 [K31l K31r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 63%nat => Z_to_bv 64 (V 63%nat) | 88%nat => Z_to_bv 64 (V 88%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 40%nat => (V 40%nat) | 57%nat => (V 57%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 63%nat => (V 63%nat) | 88%nat => (V 88%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 89%nat. }
  assert (HR: regs_ok E Pv5G12u.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G12u.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G12u.kn0).
  { unfold know_ok, Pv5G12u.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear - HV36l HV36r K18l K18r) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear - HV33l HV33r K21l K21r) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear - HV57l HV57r K23l K23r) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear - HV37l HV37r K25l K25r) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear - HV60l HV60r K27l K27r) | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K27l K27r) | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K27l K27r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear - HV88l HV88r K29l K29r) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV88l HV88r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear - HV63l HV63r K31l K31r) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV63l HV63r K31l K31r) | exact (conj K31l K31r)]. }
    apply Forall_nil. }
  destruct (Pv5G12u.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G12u.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5G12u.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G12u.ps0) with 0x943f8 in Hms. change (SR.ps_regs Pv5G12u.ps0) with (map (fun i => (i, nth i Pv5G12u.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G12u.ps0) with Pv5G12u.cells0 in Hcells. unfold Pv5G12u.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G12u.regs0 Pv5G12u.regs_out0 96 KS_v5G12u KS_v5G12u_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G12u.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G12u.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G12u.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G12u.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G12u.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G12u.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G12u.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pv5G12u.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G12u.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5G12u.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G12u.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5G12u.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV57l HV57r K23l K23r HV60l HV60r K27l K27r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G12n := LibSegY_v5G12n.
Definition KS_v5G12n : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G12n.regs0 Pv5G12n.regs_out0).
Lemma KS_v5G12n_ok : BG.kept_ok 96 Pv5G12n.regs0 Pv5G12n.regs_out0 KS_v5G12n = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G12n_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 35%nat) <= 140737488355296 -> aligned (V 35%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 35%nat) 32 -> (((V 2%nat) - 384) + 384 <= (V 35%nat) \/ (V 35%nat) + 32 <= ((V 2%nat) - 384)) ->
  ((V 35%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 35%nat)) -> ((V 35%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 35%nat)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 35%nat) / 8) + 2147450880)) -> ((((V 35%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 35%nat) / 8) + 2147450880)) ->
  ((((V 35%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 384) \/ ((V 2%nat) - 384) + 384 <= (((V 35%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 288) (V 36%nat) -> 0 <= (V 36%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 320) (((V 35%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 264) (V 33%nat) -> 0 <= (V 33%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 312) (V 57%nat) -> 0 <= (V 57%nat) <= 1 ->
  L5.u64_at RSEGS M ((V 2%nat) - 344) (V 37%nat) -> 0 <= (V 37%nat) <= 0 -> L5.u8_at RSEGS M (V 35%nat) (V 60%nat) -> 0 <= (V 60%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 35%nat) + 0) <= i < ((V 35%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93474 M) (st fx' R' 0x934dc M')
        /\ (forall x, In x KS_v5G12n -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (2 * (V 57%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ L5.u8_at RSEGS M' (V 35%nat) (Z.lor (Z.land (V 60%nat) 253) ((2 * (V 57%nat)) mod 2 ^ 64))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV40l HV40r] [HV57l HV57r] [HV58l HV58r] [HV60l HV60r] G1 G2 G8 G9 G20 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 [K18l K18r] K19 K20 [K21l K21r] K22 [K23l K23r] K24 [K25l K25r] K26 [K27l K27r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 40%nat => (V 40%nat) | 57%nat => (V 57%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E Pv5G12n.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G12n.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G12n.kn0).
  { unfold know_ok, Pv5G12n.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear - HV36l HV36r K18l K18r) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear - HV33l HV33r K21l K21r) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear - HV57l HV57r K23l K23r) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear - HV37l HV37r K25l K25r) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear - HV60l HV60r K27l K27r) | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K27l K27r) | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K27l K27r) | exact (conj K27l K27r)]. }
    apply Forall_nil. }
  destruct (Pv5G12n.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G12n.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 35%nat) + 0) <= bv_unsigned a < ((V 35%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5G12n.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G12n.ps0) with 0x934dc in Hms. change (SR.ps_regs Pv5G12n.ps0) with (map (fun i => (i, nth i Pv5G12n.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G12n.ps0) with Pv5G12n.cells0 in Hcells. unfold Pv5G12n.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G12n.regs0 Pv5G12n.regs_out0 96 KS_v5G12n KS_v5G12n_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G12n.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G12n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G12n.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G12n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G12n.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pv5G12n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G12n.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth Pv5G12n.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV35l HV35r K6l K6r K8 K11 K12 K13 K14 K15 K16) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV57l HV57r K23l K23r HV60l HV60r K27l K27r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G13 := LibSegY_v5G13.
Definition KS_v5G13 : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G13.regs0 Pv5G13.regs_out0).
Lemma KS_v5G13_ok : BG.kept_ok 96 Pv5G13.regs0 Pv5G13.regs_out0 KS_v5G13 = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G13_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 36%nat) <= 140737488355296 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 36%nat) 32 -> (((V 2%nat) - 384) + 384 <= (V 36%nat) \/ (V 36%nat) + 32 <= ((V 2%nat) - 384)) ->
  ((V 36%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 512 <= (V 36%nat)) -> ((V 36%nat) + 32 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= (V 40%nat) \/ (V 40%nat) + 512 <= (((V 36%nat) / 8) + 2147450880)) -> ((((V 36%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 64 <= (((V 36%nat) / 8) + 2147450880)) ->
  ((((V 36%nat) / 8) + 2147450880) + 4 <= ((V 2%nat) - 384) \/ ((V 2%nat) - 384) + 384 <= (((V 36%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 368) (((V 36%nat) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 328) (V 59%nat) -> 0 <= (V 59%nat) <= 2 ->
  L5.u8_at RSEGS M (V 36%nat) (V 60%nat) -> 0 <= (V 60%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 0) <= i < ((V 36%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x934bc M) (st fx' R' 0x934dc M')
        /\ (forall x, In x KS_v5G13 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = (Z.lor (Z.land (V 60%nat) 253) (V 59%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 59%nat)
        /\ L5.u8_at RSEGS M' (V 36%nat) (Z.lor (Z.land (V 60%nat) 253) (V 59%nat))).
Proof.
  intros [HV2l HV2r] [HV36l HV36r] [HV40l HV40r] [HV58l HV58r] [HV59l HV59r] [HV60l HV60r] G1 G2 G8 G9 G19 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 [K19l K19r] K20 [K21l K21r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 36%nat => (V 36%nat) | 40%nat => (V 40%nat) | 58%nat => (V 58%nat) | 59%nat => (V 59%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E Pv5G13.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G13.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G13.kn0).
  { unfold know_ok, Pv5G13.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K12 K13 K14 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear - HV59l HV59r K19l K19r) | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r K11 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV59l HV59r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk ZA ltac:(clear - HV60l HV60r K21l K21r) | clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K21l K21r) | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_nil. }
  destruct (Pv5G13.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G13.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pv5G13.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G13.ps0) with 0x934dc in Hms. change (SR.ps_regs Pv5G13.ps0) with (map (fun i => (i, nth i Pv5G13.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G13.ps0) with Pv5G13.cells0 in Hcells. unfold Pv5G13.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G13.regs0 Pv5G13.regs_out0 96 KS_v5G13 KS_v5G13_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G13.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G13.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg Pv5G13.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r K8 K11 K12 K13 K14 K15 K16) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV59l HV59r K19l K19r HV60l HV60r K21l K21r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G14ai := LibSegY_v5G14ai.
Definition KS_v5G14ai : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G14ai.regs0 Pv5G14ai.regs_out0).
Lemma KS_v5G14ai_ok : BG.kept_ok 96 Pv5G14ai.regs0 Pv5G14ai.regs_out0 KS_v5G14ai = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G14ai_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u8_at RSEGS M ((V 2%nat) - 216) (V 60%nat) -> 0 <= (V 60%nat) <= 255 ->
  Z.testbit (V 60%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x934dc M) (st fx' R' 0x934fc M')
        /\ (forall x, In x KS_v5G14ai -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV58l HV58r] [HV60l HV60r] G1 G2 G8 G9 G23 [K0l K0r] K1 K2 K3 K4 K5 K6 [K7l K7r] K8.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E Pv5G14ai.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G14ai.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G14ai.kn0).
  { unfold know_ok, Pv5G14ai.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV60l HV60r K7l K7r K8) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K7l K7r K8) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K7l K7r K8) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K7l K7r K8; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K8); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_nil. }
  destruct (Pv5G14ai.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G14ai.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pv5G14ai.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G14ai.ps0) with 0x934fc in Hms. change (SR.ps_regs Pv5G14ai.ps0) with (map (fun i => (i, nth i Pv5G14ai.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G14ai.ps0) with Pv5G14ai.cells0 in Hcells. unfold Pv5G14ai.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G14ai.regs0 Pv5G14ai.regs_out0 96 KS_v5G14ai KS_v5G14ai_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg Pv5G14ai.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G14ai.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G14ad := LibSegY_v5G14ad.
Definition KS_v5G14ad : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G14ad.regs0 Pv5G14ad.regs_out0).
Lemma KS_v5G14ad_ok : BG.kept_ok 96 Pv5G14ad.regs0 Pv5G14ad.regs_out0 KS_v5G14ad = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G14ad_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u8_at RSEGS M ((V 2%nat) - 216) (V 60%nat) -> 0 <= (V 60%nat) <= 255 ->
  Z.testbit (V 60%nat) 0 = true -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 61%nat) -> 4096 <= (V 61%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 200) (V 62%nat) ->
  1 <= (V 62%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x934dc M) (st fx' R' 0xb1048 M')
        /\ (forall x, In x KS_v5G14ad -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 603388
        /\ getr R' (reg 10) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 62%nat))).
Proof.
  intros [HV2l HV2r] [HV58l HV58r] [HV60l HV60r] [HV61l HV61r] [HV62l HV62r] G1 G2 G8 G9 G23 [K0l K0r] K1 K2 K3 K4 K5 K6 [K7l K7r] K8 K9 [K10l K10r] K11 [K12l K12r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E Pv5G14ad.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G14ad.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G14ad.kn0).
  { unfold know_ok, Pv5G14ad.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV60l HV60r K7l K7r K8) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K7l K7r K8) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K7l K7r K8) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K7l K7r K8; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K8); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV61l HV61r K10l K10r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV62l HV62r K12l K12r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  destruct (Pv5G14ad.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G14ad.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pv5G14ad.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G14ad.ps0) with 0xb1048 in Hms. change (SR.ps_regs Pv5G14ad.ps0) with (map (fun i => (i, nth i Pv5G14ad.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G14ad.ps0) with Pv5G14ad.cells0 in Hcells. unfold Pv5G14ad.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G14ad.regs0 Pv5G14ad.regs_out0 96 KS_v5G14ad KS_v5G14ad_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G14ad.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G14ad.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G14ad.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G14ad.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pv5G14ad.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G14ad.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G14bi := LibSegY_v5G14bi.
Definition KS_v5G14bi : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G14bi.regs0 Pv5G14bi.regs_out0).
Lemma KS_v5G14bi_ok : BG.kept_ok 96 Pv5G14bi.regs0 Pv5G14bi.regs_out0 KS_v5G14bi = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G14bi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u8_at RSEGS M ((V 2%nat) - 184) (V 60%nat) -> 0 <= (V 60%nat) <= 255 ->
  Z.testbit (V 60%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x934fc M) (st fx' R' 0x936e8 M')
        /\ (forall x, In x KS_v5G14bi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV58l HV58r] [HV60l HV60r] G1 G2 G8 G9 G23 [K0l K0r] K1 K2 K3 K4 K5 K6 [K7l K7r] K8.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E Pv5G14bi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G14bi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G14bi.kn0).
  { unfold know_ok, Pv5G14bi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV60l HV60r K7l K7r K8) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K7l K7r K8) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K7l K7r K8) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K7l K7r K8; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K8); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_nil. }
  destruct (Pv5G14bi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G14bi.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pv5G14bi.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G14bi.ps0) with 0x936e8 in Hms. change (SR.ps_regs Pv5G14bi.ps0) with (map (fun i => (i, nth i Pv5G14bi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G14bi.ps0) with Pv5G14bi.cells0 in Hcells. unfold Pv5G14bi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G14bi.regs0 Pv5G14bi.regs_out0 96 KS_v5G14bi KS_v5G14bi_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg Pv5G14bi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G14bi.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G14bd := LibSegY_v5G14bd.
Definition KS_v5G14bd : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G14bd.regs0 Pv5G14bd.regs_out0).
Lemma KS_v5G14bd_ok : BG.kept_ok 96 Pv5G14bd.regs0 Pv5G14bd.regs_out0 KS_v5G14bd = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G14bd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u8_at RSEGS M ((V 2%nat) - 184) (V 60%nat) -> 0 <= (V 60%nat) <= 255 ->
  Z.testbit (V 60%nat) 0 = true -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 61%nat) -> 4096 <= (V 61%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 168) (V 62%nat) ->
  1 <= (V 62%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x934fc M) (st fx' R' 0xb1048 M')
        /\ (forall x, In x KS_v5G14bd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 603420
        /\ getr R' (reg 10) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 62%nat))).
Proof.
  intros [HV2l HV2r] [HV58l HV58r] [HV60l HV60r] [HV61l HV61r] [HV62l HV62r] G1 G2 G8 G9 G23 [K0l K0r] K1 K2 K3 K4 K5 K6 [K7l K7r] K8 K9 [K10l K10r] K11 [K12l K12r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E Pv5G14bd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G14bd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G14bd.kn0).
  { unfold know_ok, Pv5G14bd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV60l HV60r K7l K7r K8) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | byte_tac ltac:(clear - HV60l HV60r K7l K7r K8) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K7l K7r K8) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K7l K7r K8; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]) K8); clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ]]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV61l HV61r K10l K10r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV62l HV62r K12l K12r) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  destruct (Pv5G14bd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G14bd.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pv5G14bd.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G14bd.ps0) with 0xb1048 in Hms. change (SR.ps_regs Pv5G14bd.ps0) with (map (fun i => (i, nth i Pv5G14bd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G14bd.ps0) with Pv5G14bd.cells0 in Hcells. unfold Pv5G14bd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pv5G14bd.regs0 Pv5G14bd.regs_out0 96 KS_v5G14bd KS_v5G14bd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pv5G14bd.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pv5G14bd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pv5G14bd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pv5G14bd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pv5G14bd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pv5G14bd.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pv5G14j := LibSegY_v5G14j.
Definition KS_v5G14j : list nat := Eval vm_compute in (BG.kept_list 96 Pv5G14j.regs0 Pv5G14j.regs_out0).
Lemma KS_v5G14j_ok : BG.kept_ok 96 Pv5G14j.regs0 Pv5G14j.regs_out0 KS_v5G14j = true. Proof. vm_compute. reflexivity. Qed.
Lemma v5G14j_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 384) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487616 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 384) 384 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x9351c M) (st fx' R' 0x936e8 M')
        /\ (forall x, In x KS_v5G14j -> getr R' (reg x) = getr R (reg x))).
Proof.
  intros [HV2l HV2r] [HV58l HV58r] G1 G2 G8 G9 G23 [K0l K0r] K1 K2 K3 K4 K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E Pv5G14j.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pv5G14j.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pv5G14j.kn0).
  { unfold know_ok, Pv5G14j.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear - HV2l HV2r K0l K0r; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | clear; first [ solve [ (repeat match goal with HD : _ \/ _ |- _ => clear HD end); lia ] | lia ] | exactA K5]. }
    apply Forall_nil. }
  destruct (Pv5G14j.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pv5G14j.NX0 with 96%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold Pv5G14j.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pv5G14j.ps0) with 0x936e8 in Hms. change (SR.ps_regs Pv5G14j.ps0) with (map (fun i => (i, nth i Pv5G14j.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pv5G14j.ps0) with Pv5G14j.cells0 in Hcells. unfold Pv5G14j.cells0 in Hcells.
  split. { exact Hms. }
  intros j Hj. apply (BG.kept_regs E E' R R' Pv5G14j.regs0 Pv5G14j.regs_out0 96 KS_v5G14j KS_v5G14j_ok HR Hag Hregs j Hj). 
Qed.
(* [comment removed for export] *)

End L5ADIVPG2.
