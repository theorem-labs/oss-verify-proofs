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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegY_amAi LibSegY_amAd LibSegY_amBi LibSegY_amBd LibSegY_amZi LibSegY_amZd LibSegY_amI LibSegY_amL LibSegY_amE.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5AMULP.
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
Module PamAi := LibSegY_amAi.
Definition KS_amAi : list nat := Eval vm_compute in (BG.kept_list 64 PamAi.regs0 PamAi.regs_out0).
Lemma KS_amAi_ok : BG.kept_ok 64 PamAi.regs0 PamAi.regs_out0 KS_amAi = true. Proof. vm_compute. reflexivity. Qed.
Lemma amAi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) ->
  L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = false -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 34%nat) ->
  0 <= (V 34%nat) <= 2 -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 42%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 112) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 112) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f3b0 M) (st fx' R' 0x8fca4 M')
        /\ (forall x, In x KS_amAi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 586868
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 34%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 911160
        /\ getr R' (reg 18) = Z_to_bv 64 10
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV42l HV42r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 [K16l K16r] K17.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 42%nat => (V 42%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PamAi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PamAi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PamAi.kn0).
  { unfold know_ok, PamAi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV35l HV35r K13l K13r K14) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | byte_tac ltac:(clear - HV35l HV35r K13l K13r K14) | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K13l K13r K14) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K13l K13r K14) | clear; lia | rewrite (L5K.land1_bit0_false (V 35%nat) ltac:(clear - HV35l HV35r K13l K13r K14; lia) K14); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K17]. }
    apply Forall_nil. }
  destruct (PamAi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PamAi.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 112) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PamAi.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PamAi.ps0) with 0x8fca4 in Hms. change (SR.ps_regs PamAi.ps0) with (map (fun i => (i, nth i PamAi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PamAi.ps0) with PamAi.cells0 in Hcells. unfold PamAi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PamAi.regs0 PamAi.regs_out0 64 KS_amAi KS_amAi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PamAi.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PamAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAi.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PamAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAi.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PamAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAi.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PamAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAi.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PamAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAi.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PamAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAi.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PamAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAi.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PamAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAi.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PamAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAi.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PamAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAi.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PamAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAi.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PamAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PamAd := LibSegY_amAd.
Definition KS_amAd : list nat := Eval vm_compute in (BG.kept_list 64 PamAd.regs0 PamAd.regs_out0).
Lemma KS_amAd_ok : BG.kept_ok 64 PamAd.regs0 PamAd.regs_out0 KS_amAd = true. Proof. vm_compute. reflexivity. Qed.
Lemma amAd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) ->
  4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 8 -> 4104 <= ((V 36%nat) + (8 * (V 37%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 2147446784) ->
  1 <= (V 37%nat) <= 134217728 -> L5.writable RSEGS M (V 36%nat) (8 * (V 37%nat)) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) (V 37%nat) -> ((V 36%nat) + (8 * (V 37%nat)) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + (V 37%nat) <= (V 36%nat)) ->
  (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= ((V 2%nat) - 128)) -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 33%nat)) -> (65536 + 6438912 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 65536) -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) ->
  0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 134217728 ->
  L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M (V 36%nat) (V 42%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 112) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 112) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f3b0 M) (st fx' R' 0x8fca4 M')
        /\ (forall x, In x KS_amAd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 586868
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 34%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 911160
        /\ getr R' (reg 18) = Z_to_bv 64 10
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV42l HV42r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 [K16l K16r] K17 K18 K19 K20 K21 K22 K23 [K24l K24r] K25 K26 [K27l K27r] K28 K29.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 42%nat => (V 42%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PamAd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PamAd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PamAd.kn0).
  { unfold know_ok, PamAd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K25) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | byte_tac ltac:(clear - HV35l HV35r K24l K24r K25) | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K25) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K25) | clear; lia | rewrite (L5K.land1_bit0_true (V 35%nat) ltac:(clear - HV35l HV35r K24l K24r K25; lia) K25); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV34l HV34r K27l K27r) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K27l K27r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22; lia | exactA K29]. }
    apply Forall_nil. }
  destruct (PamAd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PamAd.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 112) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PamAd.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PamAd.ps0) with 0x8fca4 in Hms. change (SR.ps_regs PamAd.ps0) with (map (fun i => (i, nth i PamAd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PamAd.ps0) with PamAd.cells0 in Hcells. unfold PamAd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PamAd.regs0 PamAd.regs_out0 64 KS_amAd KS_amAd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PamAd.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PamAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAd.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PamAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAd.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PamAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAd.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PamAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PamAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAd.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PamAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAd.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PamAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAd.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PamAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAd.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PamAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAd.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PamAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAd.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PamAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamAd.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PamAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PamBi := LibSegY_amBi.
Definition KS_amBi : list nat := Eval vm_compute in (BG.kept_list 64 PamBi.regs0 PamBi.regs_out0).
Lemma KS_amBi_ok : BG.kept_ok 64 PamBi.regs0 PamBi.regs_out0 KS_amBi = true. Proof. vm_compute. reflexivity. Qed.
Lemma amBi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 58%nat) -> getr R (reg 18) = Z_to_bv 64 10 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 42%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) ->
  L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = false -> 1 <= (V 34%nat) <= 2 ->
  L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 34%nat) + 1) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f474 M) (st fx' R' 0x8f4d0 M')
        /\ (forall x, In x KS_amBi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 34%nat) + 1)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 34%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) ((V 33%nat) + 16)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV42l HV42r] [HV43l HV43r] [HV58l HV58r] G1 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 [K15l K15r] K16.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PamBi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PamBi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PamBi.kn0).
  { unfold know_ok, PamBi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV35l HV35r K13l K13r K14) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | byte_tac ltac:(clear - HV35l HV35r K13l K13r K14) | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K13l K13r K14) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K13l K13r K14) | clear; lia | rewrite (L5K.land1_bit0_false (V 35%nat) ltac:(clear - HV35l HV35r K13l K13r K14; lia) K14); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV34l HV34r K15l K15r) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K16]. }
    apply Forall_nil. }
  destruct (PamBi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PamBi.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PamBi.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PamBi.ps0) with 0x8f4d0 in Hms. change (SR.ps_regs PamBi.ps0) with (map (fun i => (i, nth i PamBi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PamBi.ps0) with PamBi.cells0 in Hcells. unfold PamBi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PamBi.regs0 PamBi.regs_out0 64 KS_amBi KS_amBi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PamBi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PamBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamBi.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PamBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamBi.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PamBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamBi.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PamBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K15l K15r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PamBd := LibSegY_amBd.
Definition KS_amBd : list nat := Eval vm_compute in (BG.kept_list 64 PamBd.regs0 PamBd.regs_out0).
Lemma KS_amBd_ok : BG.kept_ok 64 PamBd.regs0 PamBd.regs_out0 KS_amBd = true. Proof. vm_compute. reflexivity. Qed.
Lemma amBd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 58%nat) -> getr R (reg 18) = Z_to_bv 64 10 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 42%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) ->
  4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 8 -> 4104 <= ((V 36%nat) + (8 * (V 37%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 2147446784) ->
  1 <= (V 37%nat) <= 134217728 -> L5.writable RSEGS M (V 36%nat) (8 * (V 37%nat)) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) (V 37%nat) -> ((V 36%nat) + (8 * (V 37%nat)) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + (V 37%nat) <= (V 36%nat)) ->
  (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= ((V 2%nat) - 128)) -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 33%nat)) -> (65536 + 6438912 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 65536) -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) ->
  0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = true -> 1 <= (V 34%nat) <= 134217728 -> 1 <= (((-1) * (V 34%nat)) + (V 37%nat)) <= 134217728 ->
  L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 34%nat) + 1) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f474 M) (st fx' R' 0x8f4d0 M')
        /\ (forall x, In x KS_amBd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 34%nat) + 1)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 34%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV42l HV42r] [HV43l HV43r] [HV58l HV58r] G1 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 [K16l K16r] K17 K18 K19 K20 K21 K22 K23 [K24l K24r] K25 [K26l K26r] [K27l K27r] K28 K29.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PamBd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PamBd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PamBd.kn0).
  { unfold know_ok, PamBd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K25) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | byte_tac ltac:(clear - HV35l HV35r K24l K24r K25) | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K25) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K25) | clear; lia | rewrite (L5K.land1_bit0_true (V 35%nat) ltac:(clear - HV35l HV35r K24l K24r K25; lia) K25); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K27l K27r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K27l K27r HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K27l K27r) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K29]. }
    apply Forall_nil. }
  destruct (PamBd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PamBd.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PamBd.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PamBd.ps0) with 0x8f4d0 in Hms. change (SR.ps_regs PamBd.ps0) with (map (fun i => (i, nth i PamBd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PamBd.ps0) with PamBd.cells0 in Hcells. unfold PamBd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PamBd.regs0 PamBd.regs_out0 64 KS_amBd KS_amBd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PamBd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PamBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamBd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PamBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamBd.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PamBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamBd.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PamBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K26l K26r K27l K27r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PamZi := LibSegY_amZi.
Definition KS_amZi : list nat := Eval vm_compute in (BG.kept_list 64 PamZi.regs0 PamZi.regs_out0).
Lemma KS_amZi_ok : BG.kept_ok 64 PamZi.regs0 PamZi.regs_out0 KS_amZi = true. Proof. vm_compute. reflexivity. Qed.
Lemma amZi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 58%nat) -> getr R (reg 18) = Z_to_bv 64 10 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 42%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) ->
  L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = false -> L5KA.zeros_at M ((((V 2%nat) - 104) / 8) + 2147450880) 1 ->
  0 <= (V 34%nat) <= 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 34%nat) + 1) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 16) -> ~ (((V 33%nat) + 16) <= bv_unsigned a < ((V 33%nat) + 16) + 8) -> ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 16) -> ~ (((V 33%nat) + 16) <= i < ((V 33%nat) + 16) + 8) -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f474 M) (st fx' R' 0x90d58 M')
        /\ (forall x, In x KS_amZi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 587172
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 587144
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) ((V 33%nat) + 16)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV42l HV42r] [HV43l HV43r] [HV58l HV58r] G1 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 [K16l K16r] K17.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PamZi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PamZi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PamZi.kn0).
  { unfold know_ok, PamZi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV35l HV35r K13l K13r K14) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | byte_tac ltac:(clear - HV35l HV35r K13l K13r K14) | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K13l K13r K14) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K13l K13r K14) | clear; lia | rewrite (L5K.land1_bit0_false (V 35%nat) ltac:(clear - HV35l HV35r K13l K13r K14; lia) K14); clear; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K17]. }
    apply Forall_nil. }
  destruct (PamZi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PamZi.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 16) -> ~ (((V 33%nat) + 16) <= bv_unsigned a < ((V 33%nat) + 16) + 8) -> ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PamZi.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PamZi.ps0) with 0x90d58 in Hms. change (SR.ps_regs PamZi.ps0) with (map (fun i => (i, nth i PamZi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PamZi.ps0) with PamZi.cells0 in Hcells. unfold PamZi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PamZi.regs0 PamZi.regs_out0 64 KS_amZi KS_amZi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PamZi.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PamZi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamZi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PamZi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamZi.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PamZi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamZi.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PamZi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamZi.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PamZi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamZi.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PamZi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamZi.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PamZi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PamZd := LibSegY_amZd.
Definition KS_amZd : list nat := Eval vm_compute in (BG.kept_list 64 PamZd.regs0 PamZd.regs_out0).
Lemma KS_amZd_ok : BG.kept_ok 64 PamZd.regs0 PamZd.regs_out0 KS_amZd = true. Proof. vm_compute. reflexivity. Qed.
Lemma amZd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 58%nat) -> getr R (reg 18) = Z_to_bv 64 10 -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 42%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) ->
  4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 8 -> 4104 <= ((V 36%nat) + (8 * (V 37%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 2147446784) ->
  1 <= (V 37%nat) <= 134217728 -> L5.writable RSEGS M (V 36%nat) (8 * (V 37%nat)) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) (V 37%nat) -> ((V 36%nat) + (8 * (V 37%nat)) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + (V 37%nat) <= (V 36%nat)) ->
  (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= ((V 2%nat) - 128)) -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 33%nat)) -> (65536 + 6438912 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 65536) -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) ->
  0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = true -> L5KA.zeros_at M ((((V 2%nat) - 104) / 8) + 2147450880) 1 -> 0 <= (V 34%nat) <= 0 ->
  L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 34%nat) + 1) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 16) -> ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 8) -> ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 16) -> ~ (((V 36%nat) + 0) <= i < ((V 36%nat) + 0) + 8) -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f474 M) (st fx' R' 0x90d58 M')
        /\ (forall x, In x KS_amZd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 587172
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' (V 36%nat) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 587144
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 36%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV42l HV42r] [HV43l HV43r] [HV58l HV58r] G1 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 [K16l K16r] K17 K18 K19 K20 K21 K22 K23 [K24l K24r] K25 K26 [K27l K27r] K28 K29.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PamZd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PamZd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PamZd.kn0).
  { unfold know_ok, PamZd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K25) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | byte_tac ltac:(clear - HV35l HV35r K24l K24r K25) | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K25) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K25) | clear; lia | rewrite (L5K.land1_bit0_true (V 35%nat) ltac:(clear - HV35l HV35r K24l K24r K25; lia) K25); clear; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K27l K27r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV34l HV34r K27l K27r) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K29]. }
    apply Forall_nil. }
  destruct (PamZd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PamZd.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 16) -> ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 8) -> ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PamZd.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PamZd.ps0) with 0x90d58 in Hms. change (SR.ps_regs PamZd.ps0) with (map (fun i => (i, nth i PamZd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PamZd.ps0) with PamZd.cells0 in Hcells. unfold PamZd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PamZd.regs0 PamZd.regs_out0 64 KS_amZd KS_amZd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PamZd.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PamZd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamZd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PamZd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamZd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PamZd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamZd.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PamZd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamZd.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PamZd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamZd.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PamZd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamZd.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PamZd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PamI := LibSegY_amI.
Definition KS_amI : list nat := Eval vm_compute in (BG.kept_list 64 PamI.regs0 PamI.regs_out0).
Lemma KS_amI_ok : BG.kept_ok 64 PamI.regs0 PamI.regs_out0 KS_amI = true. Proof. vm_compute. reflexivity. Qed.
Lemma amI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 10 -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 41%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) ->
  4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 8 -> 4104 <= ((V 36%nat) + (8 * (V 37%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 2147446784) ->
  1 <= (V 37%nat) <= 134217728 -> L5.writable RSEGS M (V 36%nat) (8 * (V 37%nat)) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) (V 37%nat) -> ((V 36%nat) + (8 * (V 37%nat)) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + (V 37%nat) <= (V 36%nat)) ->
  (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= ((V 2%nat) - 128)) -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 33%nat)) -> (65536 + 6438912 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 65536) -> 0 <= (V 41%nat) <= 18446744073709551615 ->
  0 <= (V 38%nat) <= 18446744073709551615 -> 0 <= (V 40%nat) <= 134217727 -> 1 <= (V 34%nat) <= 134217728 -> 2 <= ((V 37%nat) - (V 40%nat)) <= 134217728 ->
  L5.u64_at RSEGS M (((V 36%nat) + (8 * (V 40%nat))) + 8) (V 39%nat) -> 0 <= (V 39%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 34%nat) + 1) ->
  L5KA.zeros_at M ((((V 2%nat) - 104) / 8) + 2147450880) 1 -> 2 <= ((V 34%nat) - (V 40%nat)) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 36%nat) + (8 * (V 40%nat))) + 0) <= bv_unsigned a < (((V 36%nat) + (8 * (V 40%nat))) + 0) + 8) -> ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 36%nat) + (8 * (V 40%nat))) + 0) <= i < (((V 36%nat) + (8 * (V 40%nat))) + 0) + 8) -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f4d0 M) (st fx' R' 0x8f4d0 M')
        /\ (forall x, In x KS_amI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 587076
        /\ bv_unsigned (getr R' (reg 10)) = (((V 41%nat) + ((((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * (V 38%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 11)) = (((if ((((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * (V 38%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64) <? ((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) then 1 else 0) + (((10 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)
        /\ getr R' (reg 12) = Z_to_bv 64 ((10 * ((V 38%nat) / 4294967296)) / 4294967296)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 40%nat) + 1)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 39%nat)
        /\ bv_unsigned (getr R' (reg 22)) = (((if (((V 41%nat) + ((((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * (V 38%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) <? ((((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * (V 38%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0) + (((if ((((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * (V 38%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64) <? ((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) then 1 else 0) + (((10 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ getr R' (reg 23) = Z_to_bv 64 (10 * ((V 38%nat) / 4294967296))
        /\ bv_unsigned (getr R' (reg 24)) = ((((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * (V 38%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 25)) = ((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 587076
        /\ L5.u64_at RSEGS M' ((V 36%nat) + (8 * (V 40%nat))) (((V 41%nat) + ((((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * (V 38%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] [HV41l HV41r] [HV43l HV43r] G1 G2 G8 G9 G18 G19 G20 G21 G22 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 [K16l K16r] K17 K18 K19 K20 K21 K22 [K23l K23r] [K24l K24r] [K25l K25r] [K26l K26r] [K27l K27r] K28 [K29l K29r] K30 K31 K32 [K33l K33r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 43%nat => (V 43%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PamI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PamI.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PamI.kn0).
  { unfold know_ok, PamI.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K25l K25r K27l K27r K33l K33r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K33l K33r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r HV40l HV40r K25l K25r K33l K33r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K33l K33r) | evalEk ZA ltac:(clear - HV39l HV39r K29l K29r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K33l K33r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K33l K33r; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K33l K33r) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K31]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K33l K33r HV40l HV40r K25l K25r K27l K27r) | exact (conj K33l K33r)]. }
    apply Forall_nil. }
  destruct (PamI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PamI.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 36%nat) + (8 * (V 40%nat))) + 0) <= bv_unsigned a < (((V 36%nat) + (8 * (V 40%nat))) + 0) + 8) -> ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PamI.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K33l K33r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K33l K33r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PamI.ps0) with 0x8f4d0 in Hms. change (SR.ps_regs PamI.ps0) with (map (fun i => (i, nth i PamI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PamI.ps0) with PamI.cells0 in Hcells. unfold PamI.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PamI.regs0 PamI.regs_out0 64 KS_amI KS_amI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PamI.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PamI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamI.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PamI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PamI.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PamI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PamI.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PamI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamI.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PamI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamI.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PamI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamI.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PamI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamI.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PamI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamI.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PamI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PamI.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PamI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamI.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PamI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PamI.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PamI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K33l K33r) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PamL := LibSegY_amL.
Definition KS_amL : list nat := Eval vm_compute in (BG.kept_list 64 PamL.regs0 PamL.regs_out0).
Lemma KS_amL_ok : BG.kept_ok 64 PamL.regs0 PamL.regs_out0 KS_amL = true. Proof. vm_compute. reflexivity. Qed.
Lemma amL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 10 -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 41%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) ->
  4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 8 -> 4104 <= ((V 36%nat) + (8 * (V 37%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 2147446784) ->
  1 <= (V 37%nat) <= 134217728 -> L5.writable RSEGS M (V 36%nat) (8 * (V 37%nat)) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) (V 37%nat) -> ((V 36%nat) + (8 * (V 37%nat)) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + (V 37%nat) <= (V 36%nat)) ->
  (((V 2%nat) - 128) + 128 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= ((V 2%nat) - 128)) -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 33%nat)) -> (65536 + 6438912 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 65536) -> 0 <= (V 41%nat) <= 18446744073709551615 ->
  0 <= (V 38%nat) <= 18446744073709551615 -> 0 <= (V 40%nat) <= 134217727 -> 1 <= (V 34%nat) <= 134217728 -> 2 <= ((V 37%nat) - (V 40%nat)) <= 134217728 ->
  L5.u64_at RSEGS M (((V 36%nat) + (8 * (V 40%nat))) + 8) (V 39%nat) -> 0 <= (V 39%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 34%nat) + 1) ->
  L5KA.zeros_at M ((((V 2%nat) - 104) / 8) + 2147450880) 1 -> 1 <= ((V 34%nat) - (V 40%nat)) <= 1 -> 1 <= (((-1) * (V 34%nat)) + (V 37%nat)) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 36%nat) + (8 * (V 40%nat))) + 0) <= bv_unsigned a < (((V 36%nat) + (8 * (V 40%nat))) + 0) + 16) -> ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 36%nat) + (8 * (V 40%nat))) + 0) <= i < (((V 36%nat) + (8 * (V 40%nat))) + 0) + 16) -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f4d0 M) (st fx' R' 0x90d58 M')
        /\ (forall x, In x KS_amL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 587172
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 40%nat) + 1)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 39%nat)
        /\ bv_unsigned (getr R' (reg 22)) = (((if (((V 41%nat) + ((((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * (V 38%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) <? ((((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * (V 38%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0) + (((if ((((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * (V 38%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64) <? ((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) then 1 else 0) + (((10 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ getr R' (reg 23) = Z_to_bv 64 (10 * ((V 38%nat) / 4294967296))
        /\ bv_unsigned (getr R' (reg 24)) = ((((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * (V 38%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 25)) = ((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((8 * (V 34%nat)) + (V 36%nat)) (((if (((V 41%nat) + ((((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * (V 38%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) <? ((((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * (V 38%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0) + (((if ((((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * (V 38%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64) <? ((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) then 1 else 0) + (((10 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 587144
        /\ L5.u64_at RSEGS M' ((V 36%nat) + (8 * (V 40%nat))) (((V 41%nat) + ((((42949672960 * ((V 38%nat) / 4294967296)) mod 2 ^ 64) + ((10 * (((4294967296 * (V 38%nat)) mod 2 ^ 64) / 4294967296)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] [HV41l HV41r] [HV43l HV43r] G1 G2 G8 G9 G18 G19 G20 G21 G22 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 [K16l K16r] K17 K18 K19 K20 K21 K22 [K23l K23r] [K24l K24r] [K25l K25r] [K26l K26r] [K27l K27r] K28 [K29l K29r] K30 K31 K32 [K33l K33r] [K34l K34r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 43%nat => (V 43%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PamL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PamL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PamL.kn0).
  { unfold know_ok, PamL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r K34l K34r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K34l K34r) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K34l K34r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K34l K34r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r K34l K34r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r K34l K34r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r K34l K34r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K34l K34r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r K34l K34r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r K34l K34r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r K34l K34r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K34l K34r) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K34l K34r) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K34l K34r) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K34l K34r) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K34l K34r) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K25l K25r K27l K27r K33l K33r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K33l K33r K34l K34r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K34l K34r HV40l HV40r K25l K25r K33l K33r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K33l K33r) | evalEk ZA ltac:(clear - HV39l HV39r K29l K29r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K33l K33r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K33l K33r; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K33l K33r K34l K34r) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K31]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K33l K33r K34l K34r HV40l HV40r K25l K25r K27l K27r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K33l K33r K34l K34r HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | exact (conj K34l K34r)]. }
    apply Forall_nil. }
  destruct (PamL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PamL.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 36%nat) + (8 * (V 40%nat))) + 0) <= bv_unsigned a < (((V 36%nat) + (8 * (V 40%nat))) + 0) + 16) -> ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PamL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K33l K33r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K33l K33r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PamL.ps0) with 0x90d58 in Hms. change (SR.ps_regs PamL.ps0) with (map (fun i => (i, nth i PamL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PamL.ps0) with PamL.cells0 in Hcells. unfold PamL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PamL.regs0 PamL.regs_out0 64 KS_amL KS_amL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PamL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PamL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PamL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PamL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PamL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamL.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PamL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamL.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PamL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamL.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PamL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamL.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PamL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamL.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PamL.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PamL.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PamL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamL.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PamL.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PamL.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PamL.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K26l K26r K33l K33r K34l K34r HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K33l K33r) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PamE := LibSegY_amE.
Definition KS_amE : list nat := Eval vm_compute in (BG.kept_list 64 PamE.regs0 PamE.regs_out0).
Lemma KS_amE_ok : BG.kept_ok 64 PamE.regs0 PamE.regs_out0 KS_amE = true. Proof. vm_compute. reflexivity. Qed.
Lemma amE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 54%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8f5a4 M) (st fx' R' 0x8f5d8 M')
        /\ (forall x, In x KS_amE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] [HV52l HV52r] [HV53l HV53r] [HV54l HV54r] G1 G2 G8 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | 54%nat => (V 54%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PamE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PamE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PamE.kn0).
  { unfold know_ok, PamE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K16]. }
    apply Forall_nil. }
  destruct (PamE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PamE.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PamE.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PamE.ps0) with 0x8f5d8 in Hms. change (SR.ps_regs PamE.ps0) with (map (fun i => (i, nth i PamE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PamE.ps0) with PamE.cells0 in Hcells. unfold PamE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PamE.regs0 PamE.regs_out0 64 KS_amE KS_amE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PamE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PamE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PamE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamE.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PamE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamE.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PamE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PamE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamE.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PamE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamE.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PamE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamE.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PamE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamE.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PamE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamE.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PamE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamE.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PamE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PamE.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PamE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PamE.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PamE.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End L5AMULP.
