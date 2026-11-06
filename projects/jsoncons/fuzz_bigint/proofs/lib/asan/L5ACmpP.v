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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegZ_vcmAii LibSegZ_vcmAid LibSegZ_vcmAdi LibSegZ_vcmAdd LibSegZ_vcmB LibSegZ_vcmP LibSegZ_vcmN LibSegZ_vcmN2 LibSegZ_vcmE LibSegZ_vcmI LibSegZ_vcmJ LibSegZ_vcmZ.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5ACMPP.
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
Module PvcmAii := LibSegZ_vcmAii.
Definition KS_vcmAii : list nat := Eval vm_compute in (BG.kept_list 48 PvcmAii.regs0 PvcmAii.regs_out0).
Lemma KS_vcmAii_ok : BG.kept_ok 48 PvcmAii.regs0 PvcmAii.regs_out0 KS_vcmAii = true. Proof. vm_compute. reflexivity. Qed.
Lemma vcmAii_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 16)) -> L5.u8_at RSEGS M (V 33%nat) (V 39%nat) ->
  0 <= (V 39%nat) <= 255 -> Z.testbit (V 39%nat) 1 = false -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 35%nat) -> 1 <= (V 35%nat) <= 300 ->
  4096 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 4 ->
  (((V 2%nat) - 16) + 16 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 16)) -> L5.u8_at RSEGS M (V 34%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 1 = false ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) (V 36%nat) -> 1 <= (V 36%nat) <= 300 -> Z.testbit (V 39%nat) 0 = false -> Z.testbit (V 40%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x915c4 M) (st fx' R' 0x91684 M')
        /\ (forall x, In x KS_vcmAii -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 16)
        /\ bv_unsigned (getr R' (reg 10)) = (Z.lor (V 36%nat) (V 35%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 14) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 17) = Z_to_bv 64 (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV39l HV39r] [HV40l HV40r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 K14 [K15l K15r] [K16l K16r] K17 K18 K19 K20 K21 [K22l K22r] K23 K24 [K25l K25r] K26 K27.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PvcmAii.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvcmAii.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvcmAii.kn0).
  { unfold know_ok, PvcmAii.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K20; lia | clear - HV2l HV2r K0l K0r K10 K20; lia | clear - HV2l HV2r K0l K0r K10 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | byte_tac ltac:(clear - HV39l HV39r K12l K12r K13 K26) | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | clear; lia | rewrite (L5K.land2_bit1_false (V 39%nat) ltac:(clear - HV39l HV39r K12l K12r K13 K26; lia) K13); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear - HV35l HV35r K15l K15r) | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K27) | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | byte_tac ltac:(clear - HV40l HV40r K22l K22r K23 K27) | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K27) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K27) | clear; lia | rewrite (L5K.land2_bit1_false (V 40%nat) ltac:(clear - HV40l HV40r K22l K22r K23 K27; lia) K23); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear - HV36l HV36r K25l K25r) | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | clear; lia | rewrite (L5K.land1_bit0_false (V 39%nat) ltac:(clear - HV39l HV39r K12l K12r K13 K26; lia) K26); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K27) | clear; lia | rewrite (L5K.land1_bit0_false (V 40%nat) ltac:(clear - HV40l HV40r K22l K22r K23 K27; lia) K27); clear; lia]. }
    apply Forall_nil. }
  destruct (PvcmAii.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvcmAii.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvcmAii.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K20 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvcmAii.ps0) with 0x91684 in Hms. change (SR.ps_regs PvcmAii.ps0) with (map (fun i => (i, nth i PvcmAii.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvcmAii.ps0) with PvcmAii.cells0 in Hcells. unfold PvcmAii.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvcmAii.regs0 PvcmAii.regs_out0 48 KS_vcmAii KS_vcmAii_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvcmAii.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvcmAii.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAii.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvcmAii.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvcmAii.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvcmAii.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAii.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvcmAii.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAii.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvcmAii.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAii.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvcmAii.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAii.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvcmAii.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAii.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PvcmAii.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAii.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PvcmAii.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvcmAid := LibSegZ_vcmAid.
Definition KS_vcmAid : list nat := Eval vm_compute in (BG.kept_list 48 PvcmAid.regs0 PvcmAid.regs_out0).
Lemma KS_vcmAid_ok : BG.kept_ok 48 PvcmAid.regs0 PvcmAid.regs_out0 KS_vcmAid = true. Proof. vm_compute. reflexivity. Qed.
Lemma vcmAid_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 16)) -> L5.u8_at RSEGS M (V 33%nat) (V 39%nat) ->
  0 <= (V 39%nat) <= 255 -> Z.testbit (V 39%nat) 1 = false -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 35%nat) -> 1 <= (V 35%nat) <= 300 ->
  4096 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 4 ->
  (((V 2%nat) - 16) + 16 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 16)) -> L5.u8_at RSEGS M (V 34%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 1 = false ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) (V 36%nat) -> 1 <= (V 36%nat) <= 300 -> Z.testbit (V 39%nat) 0 = false -> Z.testbit (V 40%nat) 0 = true ->
  L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x915c4 M) (st fx' R' 0x91684 M')
        /\ (forall x, In x KS_vcmAid -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 16)
        /\ bv_unsigned (getr R' (reg 10)) = (Z.lor (V 36%nat) (V 35%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 14) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 17) = Z_to_bv 64 (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 K14 [K15l K15r] [K16l K16r] K17 K18 K19 K20 K21 [K22l K22r] K23 K24 [K25l K25r] K26 K27 K28.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PvcmAid.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvcmAid.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvcmAid.kn0).
  { unfold know_ok, PvcmAid.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K20; lia | clear - HV2l HV2r K0l K0r K10 K20; lia | clear - HV2l HV2r K0l K0r K10 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | byte_tac ltac:(clear - HV39l HV39r K12l K12r K13 K26) | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | clear; lia | rewrite (L5K.land2_bit1_false (V 39%nat) ltac:(clear - HV39l HV39r K12l K12r K13 K26; lia) K13); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear - HV35l HV35r K15l K15r) | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K27) | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | byte_tac ltac:(clear - HV40l HV40r K22l K22r K23 K27) | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K27) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K27) | clear; lia | rewrite (L5K.land2_bit1_false (V 40%nat) ltac:(clear - HV40l HV40r K22l K22r K23 K27; lia) K23); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear - HV36l HV36r K25l K25r) | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | clear; lia | rewrite (L5K.land1_bit0_false (V 39%nat) ltac:(clear - HV39l HV39r K12l K12r K13 K26; lia) K26); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K27) | clear; lia | rewrite (L5K.land1_bit0_true (V 40%nat) ltac:(clear - HV40l HV40r K22l K22r K23 K27; lia) K27); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | exactA K28]. }
    apply Forall_nil. }
  destruct (PvcmAid.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvcmAid.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvcmAid.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K20 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvcmAid.ps0) with 0x91684 in Hms. change (SR.ps_regs PvcmAid.ps0) with (map (fun i => (i, nth i PvcmAid.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvcmAid.ps0) with PvcmAid.cells0 in Hcells. unfold PvcmAid.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvcmAid.regs0 PvcmAid.regs_out0 48 KS_vcmAid KS_vcmAid_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvcmAid.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvcmAid.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAid.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvcmAid.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvcmAid.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvcmAid.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAid.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvcmAid.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAid.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvcmAid.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAid.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvcmAid.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAid.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvcmAid.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAid.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PvcmAid.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAid.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PvcmAid.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvcmAdi := LibSegZ_vcmAdi.
Definition KS_vcmAdi : list nat := Eval vm_compute in (BG.kept_list 48 PvcmAdi.regs0 PvcmAdi.regs_out0).
Lemma KS_vcmAdi_ok : BG.kept_ok 48 PvcmAdi.regs0 PvcmAdi.regs_out0 KS_vcmAdi = true. Proof. vm_compute. reflexivity. Qed.
Lemma vcmAdi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 16)) -> L5.u8_at RSEGS M (V 33%nat) (V 39%nat) ->
  0 <= (V 39%nat) <= 255 -> Z.testbit (V 39%nat) 1 = false -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 35%nat) -> 1 <= (V 35%nat) <= 300 ->
  4096 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 4 ->
  (((V 2%nat) - 16) + 16 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 16)) -> L5.u8_at RSEGS M (V 34%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 1 = false ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) (V 36%nat) -> 1 <= (V 36%nat) <= 300 -> Z.testbit (V 39%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 37%nat) ->
  Z.testbit (V 40%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x915c4 M) (st fx' R' 0x91684 M')
        /\ (forall x, In x KS_vcmAdi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 16)
        /\ bv_unsigned (getr R' (reg 10)) = (Z.lor (V 36%nat) (V 35%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 14) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 34%nat) + 16)
        /\ getr R' (reg 17) = Z_to_bv 64 (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV39l HV39r] [HV40l HV40r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 K14 [K15l K15r] [K16l K16r] K17 K18 K19 K20 K21 [K22l K22r] K23 K24 [K25l K25r] K26 K27 K28.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PvcmAdi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvcmAdi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvcmAdi.kn0).
  { unfold know_ok, PvcmAdi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K20; lia | clear - HV2l HV2r K0l K0r K10 K20; lia | clear - HV2l HV2r K0l K0r K10 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | byte_tac ltac:(clear - HV39l HV39r K12l K12r K13 K26) | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | clear; lia | rewrite (L5K.land2_bit1_false (V 39%nat) ltac:(clear - HV39l HV39r K12l K12r K13 K26; lia) K13); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear - HV35l HV35r K15l K15r) | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K28) | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | byte_tac ltac:(clear - HV40l HV40r K22l K22r K23 K28) | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K28) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K28) | clear; lia | rewrite (L5K.land2_bit1_false (V 40%nat) ltac:(clear - HV40l HV40r K22l K22r K23 K28; lia) K23); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear - HV36l HV36r K25l K25r) | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | clear; lia | rewrite (L5K.land1_bit0_true (V 39%nat) ltac:(clear - HV39l HV39r K12l K12r K13 K26; lia) K26); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K28) | clear; lia | rewrite (L5K.land1_bit0_false (V 40%nat) ltac:(clear - HV40l HV40r K22l K22r K23 K28; lia) K28); clear; lia]. }
    apply Forall_nil. }
  destruct (PvcmAdi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvcmAdi.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvcmAdi.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K20 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvcmAdi.ps0) with 0x91684 in Hms. change (SR.ps_regs PvcmAdi.ps0) with (map (fun i => (i, nth i PvcmAdi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvcmAdi.ps0) with PvcmAdi.cells0 in Hcells. unfold PvcmAdi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvcmAdi.regs0 PvcmAdi.regs_out0 48 KS_vcmAdi KS_vcmAdi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvcmAdi.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvcmAdi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAdi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvcmAdi.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvcmAdi.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvcmAdi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAdi.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvcmAdi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAdi.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvcmAdi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAdi.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvcmAdi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAdi.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvcmAdi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAdi.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PvcmAdi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAdi.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PvcmAdi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvcmAdd := LibSegZ_vcmAdd.
Definition KS_vcmAdd : list nat := Eval vm_compute in (BG.kept_list 48 PvcmAdd.regs0 PvcmAdd.regs_out0).
Lemma KS_vcmAdd_ok : BG.kept_ok 48 PvcmAdd.regs0 PvcmAdd.regs_out0 KS_vcmAdd = true. Proof. vm_compute. reflexivity. Qed.
Lemma vcmAdd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 16)) -> L5.u8_at RSEGS M (V 33%nat) (V 39%nat) ->
  0 <= (V 39%nat) <= 255 -> Z.testbit (V 39%nat) 1 = false -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 35%nat) -> 1 <= (V 35%nat) <= 300 ->
  4096 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 4 ->
  (((V 2%nat) - 16) + 16 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 16)) -> L5.u8_at RSEGS M (V 34%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 1 = false ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) (V 36%nat) -> 1 <= (V 36%nat) <= 300 -> Z.testbit (V 39%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 37%nat) ->
  Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 38%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x915c4 M) (st fx' R' 0x91684 M')
        /\ (forall x, In x KS_vcmAdd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 16)
        /\ bv_unsigned (getr R' (reg 10)) = (Z.lor (V 36%nat) (V 35%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 14) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 17) = Z_to_bv 64 (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 K14 [K15l K15r] [K16l K16r] K17 K18 K19 K20 K21 [K22l K22r] K23 K24 [K25l K25r] K26 K27 K28 K29.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PvcmAdd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvcmAdd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvcmAdd.kn0).
  { unfold know_ok, PvcmAdd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K20; lia | clear - HV2l HV2r K0l K0r K10 K20; lia | clear - HV2l HV2r K0l K0r K10 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | byte_tac ltac:(clear - HV39l HV39r K12l K12r K13 K26) | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | clear; lia | rewrite (L5K.land2_bit1_false (V 39%nat) ltac:(clear - HV39l HV39r K12l K12r K13 K26; lia) K13); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear - HV35l HV35r K15l K15r) | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | clear; lia | exact K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K28) | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | byte_tac ltac:(clear - HV40l HV40r K22l K22r K23 K28) | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K28) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K28) | clear; lia | rewrite (L5K.land2_bit1_false (V 40%nat) ltac:(clear - HV40l HV40r K22l K22r K23 K28; lia) K23); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear - HV36l HV36r K25l K25r) | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K12l K12r K13 K26) | clear; lia | rewrite (L5K.land1_bit0_true (V 39%nat) ltac:(clear - HV39l HV39r K12l K12r K13 K26; lia) K26); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K10) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV33l HV33r K6l K6r K8 K10; lia | clear - HV33l HV33r K6l K6r K8 K10; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r K23 K28) | clear; lia | rewrite (L5K.land1_bit0_true (V 40%nat) ltac:(clear - HV40l HV40r K22l K22r K23 K28; lia) K28); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K16l K16r K18 K20) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV34l HV34r K16l K16r K18 K20; lia | clear - HV34l HV34r K16l K16r K18 K20; lia | exactA K29]. }
    apply Forall_nil. }
  destruct (PvcmAdd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvcmAdd.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvcmAdd.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 K20 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvcmAdd.ps0) with 0x91684 in Hms. change (SR.ps_regs PvcmAdd.ps0) with (map (fun i => (i, nth i PvcmAdd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvcmAdd.ps0) with PvcmAdd.cells0 in Hcells. unfold PvcmAdd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvcmAdd.regs0 PvcmAdd.regs_out0 48 KS_vcmAdd KS_vcmAdd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvcmAdd.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvcmAdd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAdd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvcmAdd.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvcmAdd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvcmAdd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAdd.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvcmAdd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAdd.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvcmAdd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAdd.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvcmAdd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAdd.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvcmAdd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAdd.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PvcmAdd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmAdd.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PvcmAdd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvcmB := LibSegZ_vcmB.
Definition KS_vcmB : list nat := Eval vm_compute in (BG.kept_list 48 PvcmB.regs0 PvcmB.regs_out0).
Lemma KS_vcmB_ok : BG.kept_ok 48 PvcmB.regs0 PvcmB.regs_out0 KS_vcmB = true. Proof. vm_compute. reflexivity. Qed.
Lemma vcmB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 14) = Z_to_bv 64 (V 39%nat) -> getr R (reg 17) = Z_to_bv 64 (V 40%nat) ->
  0 <= (V 39%nat) <= 255 -> Z.testbit (V 39%nat) 1 = false -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 1 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x91688 M) (st fx' R' 0x916ac M')
        /\ (forall x, In x KS_vcmB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 17) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV39l HV39r] [HV40l HV40r] G2 G14 G17 [K0l K0r] K1 [K2l K2r] K3.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PvcmB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvcmB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvcmB.kn0).
  { unfold know_ok, PvcmB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K0l K0r K1) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K0l K0r K1) | clear; lia | rewrite (L5K.land2_bit1_false (V 39%nat) ltac:(clear - HV39l HV39r K0l K0r K1; lia) K1); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K2l K2r K3) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K2l K2r K3) | clear; lia | rewrite (L5K.land2_bit1_false (V 40%nat) ltac:(clear - HV40l HV40r K2l K2r K3; lia) K3); clear; lia]. }
    apply Forall_nil. }
  destruct (PvcmB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvcmB.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvcmB.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvcmB.ps0) with 0x916ac in Hms. change (SR.ps_regs PvcmB.ps0) with (map (fun i => (i, nth i PvcmB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvcmB.ps0) with PvcmB.cells0 in Hcells. unfold PvcmB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvcmB.regs0 PvcmB.regs_out0 48 KS_vcmB KS_vcmB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvcmB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvcmB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvcmB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvcmB.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PvcmB.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvcmP := LibSegZ_vcmP.
Definition KS_vcmP : list nat := Eval vm_compute in (BG.kept_list 48 PvcmP.regs0 PvcmP.regs_out0).
Lemma KS_vcmP_ok : BG.kept_ok 48 PvcmP.regs0 PvcmP.regs_out0 KS_vcmP = true. Proof. vm_compute. reflexivity. Qed.
Lemma vcmP_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 14) = Z_to_bv 64 0 ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x916b4 M) (st fx' R' 0x91738 M')
        /\ (forall x, In x KS_vcmP -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1).
Proof.
  intros [HV2l HV2r] G2 G14 [K0l K0r] K1 K2 K3.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PvcmP.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvcmP.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvcmP.kn0).
  { unfold know_ok, PvcmP.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_nil. }
  destruct (PvcmP.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvcmP.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvcmP.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvcmP.ps0) with 0x91738 in Hms. change (SR.ps_regs PvcmP.ps0) with (map (fun i => (i, nth i PvcmP.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvcmP.ps0) with PvcmP.cells0 in Hcells. unfold PvcmP.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvcmP.regs0 PvcmP.regs_out0 48 KS_vcmP KS_vcmP_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvcmP.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvcmP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvcmP.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvcmP.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvcmN := LibSegZ_vcmN.
Definition KS_vcmN : list nat := Eval vm_compute in (BG.kept_list 48 PvcmN.regs0 PvcmN.regs_out0).
Lemma KS_vcmN_ok : BG.kept_ok 48 PvcmN.regs0 PvcmN.regs_out0 KS_vcmN = true. Proof. vm_compute. reflexivity. Qed.
Lemma vcmN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 14) = Z_to_bv 64 0 ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x91728 M) (st fx' R' 0x91738 M')
        /\ (forall x, In x KS_vcmN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)).
Proof.
  intros [HV2l HV2r] G2 G14 [K0l K0r] K1 K2 K3.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PvcmN.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvcmN.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvcmN.kn0).
  { unfold know_ok, PvcmN.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_nil. }
  destruct (PvcmN.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvcmN.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvcmN.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvcmN.ps0) with 0x91738 in Hms. change (SR.ps_regs PvcmN.ps0) with (map (fun i => (i, nth i PvcmN.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvcmN.ps0) with PvcmN.cells0 in Hcells. unfold PvcmN.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvcmN.regs0 PvcmN.regs_out0 48 KS_vcmN KS_vcmN_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PvcmN.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvcmN.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvcmN2 := LibSegZ_vcmN2.
Definition KS_vcmN2 : list nat := Eval vm_compute in (BG.kept_list 48 PvcmN2.regs0 PvcmN2.regs_out0).
Lemma KS_vcmN2_ok : BG.kept_ok 48 PvcmN2.regs0 PvcmN2.regs_out0 KS_vcmN2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vcmN2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 14) = Z_to_bv 64 0 ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x91720 M) (st fx' R' 0x91738 M')
        /\ (forall x, In x KS_vcmN2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)).
Proof.
  intros [HV2l HV2r] G2 G14 [K0l K0r] K1 K2 K3.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PvcmN2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvcmN2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvcmN2.kn0).
  { unfold know_ok, PvcmN2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_nil. }
  destruct (PvcmN2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvcmN2.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvcmN2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvcmN2.ps0) with 0x91738 in Hms. change (SR.ps_regs PvcmN2.ps0) with (map (fun i => (i, nth i PvcmN2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvcmN2.ps0) with PvcmN2.cells0 in Hcells. unfold PvcmN2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvcmN2.regs0 PvcmN2.regs_out0 48 KS_vcmN2 KS_vcmN2_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PvcmN2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvcmN2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvcmE := LibSegZ_vcmE.
Definition KS_vcmE : list nat := Eval vm_compute in (BG.kept_list 48 PvcmE.regs0 PvcmE.regs_out0).
Lemma KS_vcmE_ok : BG.kept_ok 48 PvcmE.regs0 PvcmE.regs_out0 KS_vcmE = true. Proof. vm_compute. reflexivity. Qed.
Lemma vcmE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) -> getr R (reg 12) = Z_to_bv 64 (V 37%nat) -> getr R (reg 15) = Z_to_bv 64 (V 35%nat) -> getr R (reg 16) = Z_to_bv 64 (V 38%nat) ->
  1 <= (V 35%nat) <= 300 -> 4096 <= (V 37%nat) <= 140737488355328 -> 4096 <= (V 38%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x916bc M) (st fx' R' 0x916d8 M')
        /\ (forall x, In x KS_vcmE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (((8 * (V 35%nat)) + (V 37%nat)) - 8)
        /\ getr R' (reg 12) = Z_to_bv 64 (((8 * (V 35%nat)) + (V 38%nat)) - 8)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 35%nat) + 1)
        /\ getr R' (reg 16) = Z_to_bv 64 (((8 * (V 35%nat)) + (V 38%nat)) - 8)
        /\ getr R' (reg 17) = Z_to_bv 64 (((8 * (V 35%nat)) + (V 37%nat)) - 8)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV37l HV37r] [HV38l HV38r] G2 G11 G12 G15 G16 [K0l K0r] [K1l K1r] [K2l K2r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PvcmE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvcmE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvcmE.kn0).
  { unfold know_ok, PvcmE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_nil. }
  destruct (PvcmE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvcmE.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvcmE.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvcmE.ps0) with 0x916d8 in Hms. change (SR.ps_regs PvcmE.ps0) with (map (fun i => (i, nth i PvcmE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvcmE.ps0) with PvcmE.cells0 in Hcells. unfold PvcmE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvcmE.regs0 PvcmE.regs_out0 48 KS_vcmE KS_vcmE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvcmE.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvcmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmE.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvcmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmE.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvcmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmE.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PvcmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvcmE.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PvcmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvcmI := LibSegZ_vcmI.
Definition KS_vcmI : list nat := Eval vm_compute in (BG.kept_list 48 PvcmI.regs0 PvcmI.regs_out0).
Lemma KS_vcmI_ok : BG.kept_ok 48 PvcmI.regs0 PvcmI.regs_out0 KS_vcmI = true. Proof. vm_compute. reflexivity. Qed.
Lemma vcmI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 11) = Z_to_bv 64 (((V 37%nat) + (8 * (V 41%nat))) - 8) -> getr R (reg 12) = Z_to_bv 64 (((V 38%nat) + (8 * (V 41%nat))) - 8) -> getr R (reg 13) = Z_to_bv 64 2147450880 -> getr R (reg 14) = Z_to_bv 64 0 -> getr R (reg 15) = Z_to_bv 64 ((V 41%nat) + 1) -> getr R (reg 16) = Z_to_bv 64 (((V 38%nat) + (8 * (V 41%nat))) - 8) -> getr R (reg 17) = Z_to_bv 64 (((V 37%nat) + (8 * (V 41%nat))) - 8) ->
  L5.img_clear M 860160 880640 -> L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 37%nat) <= 140737488355328 ->
  aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + (8 * (V 35%nat)) <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) (V 35%nat) -> 4096 <= (V 38%nat) <= 140737488355328 ->
  aligned (V 38%nat) 8 -> (2147446784 + 17592186048512 <= (V 38%nat) \/ (V 38%nat) + (8 * (V 35%nat)) <= 2147446784) -> L5KA.zeros_at M (((V 38%nat) / 8) + 2147450880) (V 35%nat) -> 1 <= (V 35%nat) <= 300 ->
  1 <= (V 41%nat) <= 300 -> 0 <= ((V 35%nat) - (V 41%nat)) <= 299 -> L5.u64_at RSEGS M (((V 37%nat) + (8 * (V 41%nat))) - 8) (V 42%nat) -> 0 <= (V 42%nat) <= 18446744073709551615 ->
  L5.u64_at RSEGS M (((V 38%nat) + (8 * (V 41%nat))) - 8) (V 43%nat) -> 0 <= (V 43%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x916d8 M) (st fx' R' 0x91708 M')
        /\ (forall x, In x KS_vcmI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 6) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 41%nat)).
Proof.
  intros [HV2l HV2r] [HV35l HV35r] [HV37l HV37r] [HV38l HV38r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] G2 G11 G12 G13 G14 G15 G16 G17 K0 K1 K2 [K3l K3r] K4 K5 K6 [K7l K7r] K8 K9 K10 [K11l K11r] [K12l K12r] [K13l K13r] K14 [K15l K15r] K16 [K17l K17r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 35%nat => (V 35%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PvcmI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvcmI.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvcmI.kn0).
  { unfold know_ok, PvcmI.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K3l K3r K5) | evalEk ZA ltac:(clear - HV35l HV35r K5 K9 K11l K11r K13l K13r) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r K5) | evalEk ZA ltac:(clear - HV35l HV35r K5 K9 K11l K11r K13l K13r) | clear - HV35l HV35r K5 K9 K11l K11r K13l K13r HV37l HV37r K3l K3r; lia | clear - HV35l HV35r K5 K9 K11l K11r K13l K13r HV37l HV37r K3l K3r; lia | clear - HV35l HV35r K5 K9 K11l K11r K13l K13r HV37l HV37r K3l K3r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K7l K7r K9) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K7l K7r K9) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K7l K7r K9) | evalEk ZA ltac:(clear - HV35l HV35r K5 K9 K11l K11r K13l K13r) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K7l K7r K9) | evalEk ZA ltac:(clear - HV35l HV35r K5 K9 K11l K11r K13l K13r) | clear - HV35l HV35r K5 K9 K11l K11r K13l K13r HV38l HV38r K7l K7r; lia | clear - HV35l HV35r K5 K9 K11l K11r K13l K13r HV38l HV38r K7l K7r; lia | clear - HV35l HV35r K5 K9 K11l K11r K13l K13r HV38l HV38r K7l K7r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K5 K9 K11l K11r K13l K13r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K12l K12r K13l K13r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K5 K9 K11l K11r K13l K13r HV41l HV41r K12l K12r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K3l K3r K5 HV41l HV41r K12l K12r K13l K13r) | evalEk ZA ltac:(clear - HV42l HV42r K15l K15r) | clear - HV37l HV37r K3l K3r K5 HV41l HV41r K12l K12r K13l K13r; lia | clear - HV37l HV37r K3l K3r K5 HV41l HV41r K12l K12r K13l K13r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV38l HV38r K7l K7r K9 HV41l HV41r K12l K12r K13l K13r) | evalEk ZA ltac:(clear - HV43l HV43r K17l K17r) | clear - HV38l HV38r K7l K7r K9 HV41l HV41r K12l K12r K13l K13r; lia | clear - HV38l HV38r K7l K7r K9 HV41l HV41r K12l K12r K13l K13r; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_nil. }
  destruct (PvcmI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvcmI.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvcmI.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvcmI.ps0) with 0x91708 in Hms. change (SR.ps_regs PvcmI.ps0) with (map (fun i => (i, nth i PvcmI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvcmI.ps0) with PvcmI.cells0 in Hcells. unfold PvcmI.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvcmI.regs0 PvcmI.regs_out0 48 KS_vcmI KS_vcmI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvcmI.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PvcmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmI.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PvcmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvcmI.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvcmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvcmJ := LibSegZ_vcmJ.
Definition KS_vcmJ : list nat := Eval vm_compute in (BG.kept_list 48 PvcmJ.regs0 PvcmJ.regs_out0).
Lemma KS_vcmJ_ok : BG.kept_ok 48 PvcmJ.regs0 PvcmJ.regs_out0 KS_vcmJ = true. Proof. vm_compute. reflexivity. Qed.
Lemma vcmJ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 11) = Z_to_bv 64 (((V 37%nat) + (8 * (V 41%nat))) - 8) -> getr R (reg 12) = Z_to_bv 64 (((V 38%nat) + (8 * (V 41%nat))) - 8) -> getr R (reg 16) = Z_to_bv 64 (((V 38%nat) + (8 * (V 41%nat))) - 8) -> getr R (reg 17) = Z_to_bv 64 (((V 37%nat) + (8 * (V 41%nat))) - 8) ->
  4096 <= (V 37%nat) <= 140737488355328 -> 4096 <= (V 38%nat) <= 140737488355328 -> 1 <= (V 41%nat) <= 300 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x9170c M) (st fx' R' 0x9171c M')
        /\ (forall x, In x KS_vcmJ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 37%nat) + (8 * (V 41%nat))) - 16)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 38%nat) + (8 * (V 41%nat))) - 16)
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 38%nat) + (8 * (V 41%nat))) - 16)
        /\ getr R' (reg 17) = Z_to_bv 64 (((V 37%nat) + (8 * (V 41%nat))) - 16)).
Proof.
  intros [HV2l HV2r] [HV37l HV37r] [HV38l HV38r] [HV41l HV41r] G2 G11 G12 G16 G17 [K0l K0r] [K1l K1r] [K2l K2r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 41%nat => (V 41%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PvcmJ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvcmJ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvcmJ.kn0).
  { unfold know_ok, PvcmJ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K1l K1r) | exact (conj K1l K1r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_nil. }
  destruct (PvcmJ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvcmJ.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvcmJ.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvcmJ.ps0) with 0x9171c in Hms. change (SR.ps_regs PvcmJ.ps0) with (map (fun i => (i, nth i PvcmJ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvcmJ.ps0) with PvcmJ.cells0 in Hcells. unfold PvcmJ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvcmJ.regs0 PvcmJ.regs_out0 48 KS_vcmJ KS_vcmJ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvcmJ.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvcmJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmJ.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvcmJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmJ.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PvcmJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvcmJ.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PvcmJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvcmZ := LibSegZ_vcmZ.
Definition KS_vcmZ : list nat := Eval vm_compute in (BG.kept_list 48 PvcmZ.regs0 PvcmZ.regs_out0).
Lemma KS_vcmZ_ok : BG.kept_ok 48 PvcmZ.regs0 PvcmZ.regs_out0 KS_vcmZ = true. Proof. vm_compute. reflexivity. Qed.
Lemma vcmZ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 14) = Z_to_bv 64 0 -> getr R (reg 15) = Z_to_bv 64 1 ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x916d8 M) (st fx' R' 0x91738 M')
        /\ (forall x, In x KS_vcmZ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] G2 G14 G15 [K0l K0r] K1 K2 K3.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PvcmZ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvcmZ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvcmZ.kn0).
  { unfold know_ok, PvcmZ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_nil. }
  destruct (PvcmZ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvcmZ.NX0 with 48%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvcmZ.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvcmZ.ps0) with 0x91738 in Hms. change (SR.ps_regs PvcmZ.ps0) with (map (fun i => (i, nth i PvcmZ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvcmZ.ps0) with PvcmZ.cells0 in Hcells. unfold PvcmZ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvcmZ.regs0 PvcmZ.regs_out0 48 KS_vcmZ KS_vcmZ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvcmZ.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvcmZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvcmZ.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvcmZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvcmZ.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvcmZ.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End L5ACMPP.
