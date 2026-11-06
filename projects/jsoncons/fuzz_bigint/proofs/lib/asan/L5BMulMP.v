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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegY_vmmAi LibSegY_vmmAd LibSegY_vmmBi LibSegY_vmmBd LibSegY_vmmI LibSegY_vmmL LibSegY_vmmE.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5AMULMP.
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
Module PvmmAi := LibSegY_vmmAi.
Definition KS_vmmAi : list nat := Eval vm_compute in (BG.kept_list 64 PvmmAi.regs0 PvmmAi.regs_out0).
Lemma KS_vmmAi_ok : BG.kept_ok 64 PvmmAi.regs0 PvmmAi.regs_out0 KS_vmmAi = true. Proof. vm_compute. reflexivity. Qed.
Lemma vmmAi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 60%nat) ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 160)) ->
  0 <= (V 60%nat) <= 18446744073709551615 -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = false ->
  L5.u64_at RSEGS M ((V 33%nat) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 2 -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 42%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 144) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 144) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x94830 M) (st fx' R' 0x8fca4 M')
        /\ (forall x, In x KS_vmmAi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 608512
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 144)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 34%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 911160
        /\ getr R' (reg 18) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 34%nat)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV42l HV42r] [HV60l HV60r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 K16 [K17l K17r] K18.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 42%nat => (V 42%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PvmmAi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvmmAi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvmmAi.kn0).
  { unfold know_ok, PvmmAi.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV35l HV35r K14l K14r K15) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | byte_tac ltac:(clear - HV35l HV35r K14l K14r K15) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K14l K14r K15) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K14l K14r K15) | clear; lia | rewrite (L5K.land1_bit0_false (V 35%nat) ltac:(clear - HV35l HV35r K14l K14r K15; lia) K15); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV34l HV34r K17l K17r) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K18]. }
    apply Forall_nil. }
  destruct (PvmmAi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvmmAi.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 144) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvmmAi.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvmmAi.ps0) with 0x8fca4 in Hms. change (SR.ps_regs PvmmAi.ps0) with (map (fun i => (i, nth i PvmmAi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvmmAi.ps0) with PvmmAi.cells0 in Hcells. unfold PvmmAi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvmmAi.regs0 PvmmAi.regs_out0 64 KS_vmmAi KS_vmmAi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvmmAi.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvmmAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAi.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvmmAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAi.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvmmAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAi.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvmmAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAi.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvmmAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAi.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvmmAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAi.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PvmmAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAi.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PvmmAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAi.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PvmmAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAi.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PvmmAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAi.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PvmmAi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvmmAd := LibSegY_vmmAd.
Definition KS_vmmAd : list nat := Eval vm_compute in (BG.kept_list 64 PvmmAd.regs0 PvmmAd.regs_out0).
Lemma KS_vmmAd_ok : BG.kept_ok 64 PvmmAd.regs0 PvmmAd.regs_out0 KS_vmmAd = true. Proof. vm_compute. reflexivity. Qed.
Lemma vmmAd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 60%nat) ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 160)) ->
  4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 8 -> 4104 <= ((V 36%nat) + (8 * (V 37%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 2147446784) ->
  1 <= (V 37%nat) <= 134217728 -> L5.writable RSEGS M (V 36%nat) (8 * (V 37%nat)) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) (V 37%nat) -> ((V 36%nat) + (8 * (V 37%nat)) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + (V 37%nat) <= (V 36%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= ((V 2%nat) - 160)) -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 33%nat)) -> (65536 + 6438912 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 65536) -> 0 <= (V 60%nat) <= 18446744073709551615 ->
  L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 34%nat) ->
  0 <= (V 34%nat) <= 134217728 -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M (V 36%nat) (V 42%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 144) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 144) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x94830 M) (st fx' R' 0x8fca4 M')
        /\ (forall x, In x KS_vmmAd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 608512
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 144)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 34%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 911160
        /\ getr R' (reg 18) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 20) = Z_to_bv 64 2147450880
        /\ getr R' (reg 21) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 34%nat)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV42l HV42r] [HV60l HV60r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 [K16l K16r] K17 K18 K19 K20 K21 K22 [K23l K23r] K24 [K25l K25r] K26 K27 [K28l K28r] K29 K30.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 42%nat => (V 42%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PvmmAd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvmmAd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvmmAd.kn0).
  { unfold know_ok, PvmmAd.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV35l HV35r K25l K25r K26) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | byte_tac ltac:(clear - HV35l HV35r K25l K25r K26) | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K25l K25r K26) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K25l K25r K26) | clear; lia | rewrite (L5K.land1_bit0_true (V 35%nat) ltac:(clear - HV35l HV35r K25l K25r K26; lia) K26); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV34l HV34r K28l K28r) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22; lia | exactA K30]. }
    apply Forall_nil. }
  destruct (PvmmAd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvmmAd.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 144) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvmmAd.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvmmAd.ps0) with 0x8fca4 in Hms. change (SR.ps_regs PvmmAd.ps0) with (map (fun i => (i, nth i PvmmAd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvmmAd.ps0) with PvmmAd.cells0 in Hcells. unfold PvmmAd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvmmAd.regs0 PvmmAd.regs_out0 64 KS_vmmAd KS_vmmAd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvmmAd.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvmmAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAd.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvmmAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAd.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvmmAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvmmAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAd.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvmmAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAd.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvmmAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAd.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PvmmAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAd.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PvmmAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAd.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PvmmAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAd.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PvmmAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmAd.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PvmmAd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K28l K28r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvmmBi := LibSegY_vmmBi.
Definition KS_vmmBi : list nat := Eval vm_compute in (BG.kept_list 64 PvmmBi.regs0 PvmmBi.regs_out0).
Lemma KS_vmmBi_ok : BG.kept_ok 64 PvmmBi.regs0 PvmmBi.regs_out0 KS_vmmBi = true. Proof. vm_compute. reflexivity. Qed.
Lemma vmmBi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 10) = Z_to_bv 64 (V 58%nat) -> getr R (reg 18) = Z_to_bv 64 (V 60%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 42%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 160)) ->
  0 <= (V 60%nat) <= 18446744073709551615 -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 ->
  Z.testbit (V 35%nat) 0 = false -> 1 <= (V 34%nat) <= 2 -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 34%nat) + 1) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x94900 M) (st fx' R' 0x94970 M')
        /\ (forall x, In x KS_vmmBi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551615
        /\ bv_unsigned (getr R' (reg 11)) = ((4294967296 * (V 60%nat)) mod 2 ^ 64)
        /\ getr R' (reg 18) = Z_to_bv 64 4294967295
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 60%nat) / 4294967296)
        /\ bv_unsigned (getr R' (reg 23)) = (((4294967296 * (V 60%nat)) mod 2 ^ 64) / 4294967296)
        /\ getr R' (reg 24) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 34%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 34%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV42l HV42r] [HV43l HV43r] [HV58l HV58r] [HV60l HV60r] G1 G2 G8 G10 G18 G19 G20 G21 G22 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 K14 [K15l K15r] K16 [K17l K17r] K18.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PvmmBi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvmmBi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvmmBi.kn0).
  { unfold know_ok, PvmmBi.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear - HV34l HV34r K17l K17r) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV35l HV35r K15l K15r K16) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | byte_tac ltac:(clear - HV35l HV35r K15l K15r K16) | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K15l K15r K16) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K15l K15r K16) | clear; lia | rewrite (L5K.land1_bit0_false (V 35%nat) ltac:(clear - HV35l HV35r K15l K15r K16; lia) K16); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV34l HV34r K17l K17r) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K18]. }
    apply Forall_nil. }
  destruct (PvmmBi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvmmBi.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 32) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvmmBi.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvmmBi.ps0) with 0x94970 in Hms. change (SR.ps_regs PvmmBi.ps0) with (map (fun i => (i, nth i PvmmBi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvmmBi.ps0) with PvmmBi.cells0 in Hcells. unfold PvmmBi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvmmBi.regs0 PvmmBi.regs_out0 64 KS_vmmBi KS_vmmBi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvmmBi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvmmBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmBi.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvmmBi.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvmmBi.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvmmBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmBi.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PvmmBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmBi.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PvmmBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmBi.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PvmmBi.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvmmBi.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PvmmBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K17l K17r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K17l K17r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvmmBd := LibSegY_vmmBd.
Definition KS_vmmBd : list nat := Eval vm_compute in (BG.kept_list 64 PvmmBd.regs0 PvmmBd.regs_out0).
Lemma KS_vmmBd_ok : BG.kept_ok 64 PvmmBd.regs0 PvmmBd.regs_out0 KS_vmmBd = true. Proof. vm_compute. reflexivity. Qed.
Lemma vmmBd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 10) = Z_to_bv 64 (V 58%nat) -> getr R (reg 18) = Z_to_bv 64 (V 60%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 42%nat) -> getr R (reg 22) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 160)) ->
  4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 8 -> 4104 <= ((V 36%nat) + (8 * (V 37%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 2147446784) ->
  1 <= (V 37%nat) <= 134217728 -> L5.writable RSEGS M (V 36%nat) (8 * (V 37%nat)) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) (V 37%nat) -> ((V 36%nat) + (8 * (V 37%nat)) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + (V 37%nat) <= (V 36%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= ((V 2%nat) - 160)) -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 33%nat)) -> (65536 + 6438912 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 65536) -> 0 <= (V 60%nat) <= 18446744073709551615 ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = true ->
  1 <= (V 34%nat) <= 134217728 -> 1 <= (((-1) * (V 34%nat)) + (V 37%nat)) <= 134217728 -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 34%nat) + 1) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x94900 M) (st fx' R' 0x94970 M')
        /\ (forall x, In x KS_vmmBd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 18446744073709551615
        /\ bv_unsigned (getr R' (reg 11)) = ((4294967296 * (V 60%nat)) mod 2 ^ 64)
        /\ getr R' (reg 18) = Z_to_bv 64 4294967295
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 60%nat) / 4294967296)
        /\ bv_unsigned (getr R' (reg 23)) = (((4294967296 * (V 60%nat)) mod 2 ^ 64) / 4294967296)
        /\ getr R' (reg 24) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 34%nat) + 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 34%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV42l HV42r] [HV43l HV43r] [HV58l HV58r] [HV60l HV60r] G1 G2 G8 G10 G18 G19 G20 G21 G22 G23 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 [K16l K16r] K17 K18 K19 K20 K21 K22 [K23l K23r] K24 K25 [K26l K26r] K27 [K28l K28r] [K29l K29r] K30 K31.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PvmmBd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvmmBd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvmmBd.kn0).
  { unfold know_ok, PvmmBd.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K29l K29r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K29l K29r) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K29l K29r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K29l K29r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K29l K29r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K29l K29r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K29l K29r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K29l K29r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K29l K29r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K29l K29r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K29l K29r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K29l K29r) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K29l K29r) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K29l K29r) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K29l K29r) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K29l K29r) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear - HV34l HV34r K28l K28r K29l K29r) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K27) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | byte_tac ltac:(clear - HV35l HV35r K26l K26r K27) | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K27) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K26l K26r K27) | clear; lia | rewrite (L5K.land1_bit0_true (V 35%nat) ltac:(clear - HV35l HV35r K26l K26r K27; lia) K27); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K28l K28r K29l K29r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K28l K28r K29l K29r HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV34l HV34r K28l K28r K29l K29r) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K31]. }
    apply Forall_nil. }
  destruct (PvmmBd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvmmBd.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 32) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvmmBd.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvmmBd.ps0) with 0x94970 in Hms. change (SR.ps_regs PvmmBd.ps0) with (map (fun i => (i, nth i PvmmBd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvmmBd.ps0) with PvmmBd.cells0 in Hcells. unfold PvmmBd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvmmBd.regs0 PvmmBd.regs_out0 64 KS_vmmBd KS_vmmBd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvmmBd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvmmBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmBd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvmmBd.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvmmBd.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvmmBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmBd.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PvmmBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmBd.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PvmmBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmBd.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PvmmBd.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvmmBd.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PvmmBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K28l K28r K29l K29r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K28l K28r K29l K29r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvmmI := LibSegY_vmmI.
Definition KS_vmmI : list nat := Eval vm_compute in (BG.kept_list 64 PvmmI.regs0 PvmmI.regs_out0).
Lemma KS_vmmI_ok : BG.kept_ok 64 PvmmI.regs0 PvmmI.regs_out0 KS_vmmI = true. Proof. vm_compute. reflexivity. Qed.
Lemma vmmI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 18) = Z_to_bv 64 4294967295 -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 61%nat) -> getr R (reg 23) = Z_to_bv 64 (V 62%nat) -> getr R (reg 24) = Z_to_bv 64 (V 41%nat) ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 160)) ->
  4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 8 -> 4104 <= ((V 36%nat) + (8 * (V 37%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 2147446784) ->
  1 <= (V 37%nat) <= 134217728 -> L5.writable RSEGS M (V 36%nat) (8 * (V 37%nat)) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) (V 37%nat) -> ((V 36%nat) + (8 * (V 37%nat)) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + (V 37%nat) <= (V 36%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= ((V 2%nat) - 160)) -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 33%nat)) -> (65536 + 6438912 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 65536) -> 0 <= (V 41%nat) <= 18446744073709551615 ->
  0 <= (V 38%nat) <= 18446744073709551615 -> 0 <= (V 40%nat) <= 134217727 -> 1 <= (V 34%nat) <= 134217728 -> 2 <= ((V 37%nat) - (V 40%nat)) <= 134217728 ->
  L5.u64_at RSEGS M (((V 36%nat) + (8 * (V 40%nat))) + 8) (V 39%nat) -> 0 <= (V 39%nat) <= 18446744073709551615 -> 0 <= (V 61%nat) <= 4294967295 -> 0 <= (V 62%nat) <= 4294967295 ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 34%nat) + 1) -> L5KA.zeros_at M ((((V 2%nat) - 120) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) ->
  2 <= ((V 34%nat) - (V 40%nat)) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 36%nat) + (8 * (V 40%nat))) + 0) <= bv_unsigned a < (((V 36%nat) + (8 * (V 40%nat))) + 0) + 8) -> ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 36%nat) + (8 * (V 40%nat))) + 0) <= i < (((V 36%nat) + (8 * (V 40%nat))) + 0) + 8) -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x94970 M) (st fx' R' 0x94970 M')
        /\ (forall x, In x KS_vmmI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 608744
        /\ bv_unsigned (getr R' (reg 8)) = ((((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64) / 4294967296)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 38%nat) / 4294967296)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ bv_unsigned (getr R' (reg 11)) = (((if ((((4294967296 * ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) + ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) <? ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0) + (((if ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) <? ((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0) + (((((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64) / 4294967296) + ((((((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64) / 4294967296) + ((((V 38%nat) / 4294967296) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 12)) = (if ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) <? ((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0)
        /\ bv_unsigned (getr R' (reg 13)) = (((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64) / 4294967296)
        /\ bv_unsigned (getr R' (reg 14)) = (if ((((4294967296 * ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) + ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) <? ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 40%nat) + 1)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 39%nat)
        /\ bv_unsigned (getr R' (reg 24)) = (((if (((V 41%nat) + ((((4294967296 * ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) + ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) <? ((((4294967296 * ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) + ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0) + (((if ((((4294967296 * ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) + ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) <? ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0) + (((if ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) <? ((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0) + (((((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64) / 4294967296) + ((((((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64) / 4294967296) + ((((V 38%nat) / 4294967296) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 25)) = ((((4294967296 * ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) + ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 26)) = ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 27)) = ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 608744
        /\ L5.u64_at RSEGS M' ((V 36%nat) + (8 * (V 40%nat))) (((V 41%nat) + ((((4294967296 * ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) + ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] [HV41l HV41r] [HV43l HV43r] [HV61l HV61r] [HV62l HV62r] G1 G2 G18 G19 G20 G21 G22 G23 G24 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 [K16l K16r] K17 K18 K19 K20 K21 K22 [K23l K23r] [K24l K24r] [K25l K25r] [K26l K26r] [K27l K27r] K28 [K29l K29r] [K30l K30r] [K31l K31r] K32 K33 K34 K35 [K36l K36r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 43%nat => (V 43%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E PvmmI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvmmI.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvmmI.kn0).
  { unfold know_ok, PvmmI.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K25l K25r K27l K27r K36l K36r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K36l K36r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r HV40l HV40r K25l K25r K36l K36r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K36l K36r) | evalEk ZA ltac:(clear - HV39l HV39r K29l K29r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K36l K36r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K36l K36r; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K30l K30r) | exact (conj K30l K30r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K31l K31r) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K36l K36r) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K33]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K36l K36r) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K36l K36r HV40l HV40r K25l K25r K27l K27r) | exact (conj K36l K36r)]. }
    apply Forall_nil. }
  destruct (PvmmI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvmmI.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 36%nat) + (8 * (V 40%nat))) + 0) <= bv_unsigned a < (((V 36%nat) + (8 * (V 40%nat))) + 0) + 8) -> ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PvmmI.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K36l K36r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K36l K36r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvmmI.ps0) with 0x94970 in Hms. change (SR.ps_regs PvmmI.ps0) with (map (fun i => (i, nth i PvmmI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvmmI.ps0) with PvmmI.cells0 in Hcells. unfold PvmmI.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvmmI.regs0 PvmmI.regs_out0 64 KS_vmmI KS_vmmI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvmmI.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvmmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmI.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvmmI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvmmI.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvmmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmI.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvmmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmI.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvmmI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvmmI.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvmmI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvmmI.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvmmI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvmmI.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvmmI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvmmI.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PvmmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmI.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PvmmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmI.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PvmmI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvmmI.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PvmmI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvmmI.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PvmmI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvmmI.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PvmmI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K36l K36r) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvmmL := LibSegY_vmmL.
Definition KS_vmmL : list nat := Eval vm_compute in (BG.kept_list 64 PvmmL.regs0 PvmmL.regs_out0).
Lemma KS_vmmL_ok : BG.kept_ok 64 PvmmL.regs0 PvmmL.regs_out0 KS_vmmL = true. Proof. vm_compute. reflexivity. Qed.
Lemma vmmL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 18) = Z_to_bv 64 4294967295 -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 38%nat) -> getr R (reg 22) = Z_to_bv 64 (V 61%nat) -> getr R (reg 23) = Z_to_bv 64 (V 62%nat) -> getr R (reg 24) = Z_to_bv 64 (V 41%nat) ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 160)) ->
  4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 8 -> 4104 <= ((V 36%nat) + (8 * (V 37%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 2147446784) ->
  1 <= (V 37%nat) <= 134217728 -> L5.writable RSEGS M (V 36%nat) (8 * (V 37%nat)) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) (V 37%nat) -> ((V 36%nat) + (8 * (V 37%nat)) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + (V 37%nat) <= (V 36%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= ((V 2%nat) - 160)) -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 33%nat)) -> (65536 + 6438912 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 65536) -> 0 <= (V 41%nat) <= 18446744073709551615 ->
  0 <= (V 38%nat) <= 18446744073709551615 -> 0 <= (V 40%nat) <= 134217727 -> 1 <= (V 34%nat) <= 134217728 -> 2 <= ((V 37%nat) - (V 40%nat)) <= 134217728 ->
  L5.u64_at RSEGS M (((V 36%nat) + (8 * (V 40%nat))) + 8) (V 39%nat) -> 0 <= (V 39%nat) <= 18446744073709551615 -> 0 <= (V 61%nat) <= 4294967295 -> 0 <= (V 62%nat) <= 4294967295 ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) (V 36%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 34%nat) + 1) -> L5KA.zeros_at M ((((V 2%nat) - 120) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 34%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) -> 1 <= ((V 34%nat) - (V 40%nat)) <= 1 -> 1 <= (((-1) * (V 34%nat)) + (V 37%nat)) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 36%nat) + (8 * (V 40%nat))) + 0) <= bv_unsigned a < (((V 36%nat) + (8 * (V 40%nat))) + 0) + 16) -> ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 36%nat) + (8 * (V 40%nat))) + 0) <= i < (((V 36%nat) + (8 * (V 40%nat))) + 0) + 16) -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x94970 M) (st fx' R' 0x90d58 M')
        /\ (forall x, In x KS_vmmL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 608880
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 38%nat) / 4294967296)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 40%nat) + 1)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 39%nat)
        /\ bv_unsigned (getr R' (reg 24)) = (((if (((V 41%nat) + ((((4294967296 * ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) + ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) <? ((((4294967296 * ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) + ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0) + (((if ((((4294967296 * ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) + ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) <? ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0) + (((if ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) <? ((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0) + (((((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64) / 4294967296) + ((((((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64) / 4294967296) + ((((V 38%nat) / 4294967296) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 25)) = ((((4294967296 * ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) + ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 26)) = ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ bv_unsigned (getr R' (reg 27)) = ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((8 * (V 34%nat)) + (V 36%nat)) (((if (((V 41%nat) + ((((4294967296 * ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) + ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) <? ((((4294967296 * ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) + ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0) + (((if ((((4294967296 * ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) + ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) <? ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0) + (((if ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) <? ((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) then 1 else 0) + (((((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64) / 4294967296) + ((((((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64) / 4294967296) + ((((V 38%nat) / 4294967296) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 608848
        /\ L5.u64_at RSEGS M' ((V 36%nat) + (8 * (V 40%nat))) (((V 41%nat) + ((((4294967296 * ((((V 38%nat) / 4294967296) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64) + ((((4294967296 * (((Z.land (V 38%nat) 4294967295) * (V 61%nat)) mod 2 ^ 64)) mod 2 ^ 64) + (((Z.land (V 38%nat) 4294967295) * (V 62%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] [HV41l HV41r] [HV43l HV43r] [HV61l HV61r] [HV62l HV62r] G1 G2 G18 G19 G20 G21 G22 G23 G24 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 [K16l K16r] K17 K18 K19 K20 K21 K22 [K23l K23r] [K24l K24r] [K25l K25r] [K26l K26r] [K27l K27r] K28 [K29l K29r] [K30l K30r] [K31l K31r] K32 K33 K34 K35 K36 [K37l K37r] [K38l K38r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 43%nat => (V 43%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E PvmmL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvmmL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvmmL.kn0).
  { unfold know_ok, PvmmL.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r K38l K38r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K38l K38r) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K38l K38r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K38l K38r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r K38l K38r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r K38l K38r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r K38l K38r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K38l K38r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r K38l K38r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r K38l K38r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV37l HV37r K16l K16r K27l K27r K38l K38r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K38l K38r) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K38l K38r) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K38l K38r) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K38l K38r) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K38l K38r) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K25l K25r K27l K27r K37l K37r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K37l K37r K38l K38r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r K38l K38r HV40l HV40r K25l K25r K37l K37r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K37l K37r) | evalEk ZA ltac:(clear - HV39l HV39r K29l K29r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K37l K37r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K37l K37r; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K30l K30r) | exact (conj K30l K30r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K31l K31r) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K37l K37r K38l K38r) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K33]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K37l K37r K38l K38r) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K37l K37r K38l K38r HV40l HV40r K25l K25r K27l K27r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K37l K37r K38l K38r HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K22 K27l K27r) | exact (conj K38l K38r)]. }
    apply Forall_nil. }
  destruct (PvmmL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvmmL.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 36%nat) + (8 * (V 40%nat))) + 0) <= bv_unsigned a < (((V 36%nat) + (8 * (V 40%nat))) + 0) + 16) -> ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PvmmL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K37l K37r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K37l K37r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvmmL.ps0) with 0x90d58 in Hms. change (SR.ps_regs PvmmL.ps0) with (map (fun i => (i, nth i PvmmL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvmmL.ps0) with PvmmL.cells0 in Hcells. unfold PvmmL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvmmL.regs0 PvmmL.regs_out0 64 KS_vmmL KS_vmmL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvmmL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvmmL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmL.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvmmL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmL.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvmmL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvmmL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvmmL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvmmL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmL.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvmmL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmL.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvmmL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmL.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PvmmL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmL.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PvmmL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmL.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PvmmL.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvmmL.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PvmmL.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvmmL.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PvmmL.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvmmL.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PvmmL.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K26l K26r K37l K37r K38l K38r HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 K22 HV40l HV40r K25l K25r K27l K27r K37l K37r) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvmmE := LibSegY_vmmE.
Definition KS_vmmE : list nat := Eval vm_compute in (BG.kept_list 64 PvmmE.regs0 PvmmE.regs_out0).
Lemma KS_vmmE_ok : BG.kept_ok 64 PvmmE.regs0 PvmmE.regs_out0 KS_vmmE = true. Proof. vm_compute. reflexivity. Qed.
Lemma vmmE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 56%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x94a70 M) (st fx' R' 0x94aac M')
        /\ (forall x, In x KS_vmmE -> getr R' (reg x) = getr R (reg x))
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
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 56%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] [HV52l HV52r] [HV53l HV53r] [HV54l HV54r] [HV55l HV55r] [HV56l HV56r] G1 G2 G8 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | 55%nat => Z_to_bv 64 (V 55%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | 54%nat => (V 54%nat) | 55%nat => (V 55%nat) | 56%nat => (V 56%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PvmmE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvmmE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvmmE.kn0).
  { unfold know_ok, PvmmE.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K18]. }
    apply Forall_nil. }
  destruct (PvmmE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvmmE.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvmmE.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvmmE.ps0) with 0x94aac in Hms. change (SR.ps_regs PvmmE.ps0) with (map (fun i => (i, nth i PvmmE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvmmE.ps0) with PvmmE.cells0 in Hcells. unfold PvmmE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvmmE.regs0 PvmmE.regs_out0 64 KS_vmmE KS_vmmE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvmmE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvmmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvmmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmE.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvmmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmE.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvmmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvmmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmE.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvmmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmE.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PvmmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmE.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PvmmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmE.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PvmmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmE.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PvmmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmE.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PvmmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmE.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PvmmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmE.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PvmmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvmmE.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PvmmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvmmE.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PvmmE.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End L5AMULMP.
