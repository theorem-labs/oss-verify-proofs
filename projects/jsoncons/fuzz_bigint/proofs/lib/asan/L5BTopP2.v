(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigLinkZA.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Bo0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegY_tpKi LibSegY_tpKd LibSegY_tpLi LibSegY_tpLd LibSegY_tpMi LibSegY_tpMd LibSegY_tpNi LibSegY_tpNd LibSegY_tpN2 LibSegY_tpOi LibSegY_tpOd LibSegY_tpO2 LibSegY_tpPs LibSegY_tpPl LibSegY_tpPl2 LibSegY_tpQ1 LibSegY_tpQt LibSegY_tpQ20 LibSegY_tpQ216.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5ATP2.
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
Module PtpKi := LibSegY_tpKi.
Definition KS_tpKi : list nat := Eval vm_compute in (BG.kept_list 64 PtpKi.regs0 PtpKi.regs_out0).
Lemma KS_tpKi_ok : BG.kept_ok 64 PtpKi.regs0 PtpKi.regs_out0 KS_tpKi = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpKi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 288) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M ((V 40%nat) + 288) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e344 M) (st fx' R' 0x8e364 M')
        /\ (forall x, In x KS_tpKi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV60l HV60r] G1 G2 G9 G18 G19 G20 G21 G23 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] K21.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PtpKi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpKi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpKi.kn0).
  { unfold know_ok, PtpKi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_nil. }
  destruct (PtpKi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpKi.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpKi.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpKi.ps0) with 0x8e364 in Hms. change (SR.ps_regs PtpKi.ps0) with (map (fun i => (i, nth i PtpKi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpKi.ps0) with PtpKi.cells0 in Hcells. unfold PtpKi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpKi.regs0 PtpKi.regs_out0 64 KS_tpKi KS_tpKi_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PtpKi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpKi.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpKd := LibSegY_tpKd.
Definition KS_tpKd : list nat := Eval vm_compute in (BG.kept_list 64 PtpKd.regs0 PtpKd.regs_out0).
Lemma KS_tpKd_ok : BG.kept_ok 64 PtpKd.regs0 PtpKd.regs_out0 KS_tpKd = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpKd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 288) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M ((V 40%nat) + 288) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = true -> L5.u64_at RSEGS M ((V 40%nat) + 312) (V 61%nat) -> 4096 <= (V 61%nat) <= 140737488355328 ->
  L5.u64_at RSEGS M ((V 40%nat) + 304) (V 62%nat) -> 1 <= (V 62%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e344 M) (st fx' R' 0xb1048 M')
        /\ (forall x, In x KS_tpKd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582500
        /\ getr R' (reg 10) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 62%nat))).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV60l HV60r] [HV61l HV61r] [HV62l HV62r] G1 G2 G9 G18 G19 G20 G21 G23 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] K21 K22 [K23l K23r] K24 [K25l K25r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E PtpKd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpKd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpKd.kn0).
  { unfold know_ok, PtpKd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV61l HV61r K23l K23r) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV62l HV62r K25l K25r) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  destruct (PtpKd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpKd.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpKd.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpKd.ps0) with 0xb1048 in Hms. change (SR.ps_regs PtpKd.ps0) with (map (fun i => (i, nth i PtpKd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpKd.ps0) with PtpKd.cells0 in Hcells. unfold PtpKd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpKd.regs0 PtpKd.regs_out0 64 KS_tpKd KS_tpKd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpKd.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpKd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpKd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpKd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtpKd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpKd.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpLi := LibSegY_tpLi.
Definition KS_tpLi : list nat := Eval vm_compute in (BG.kept_list 64 PtpLi.regs0 PtpLi.regs_out0).
Lemma KS_tpLi_ok : BG.kept_ok 64 PtpLi.regs0 PtpLi.regs_out0 KS_tpLi = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpLi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 288) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M ((V 2%nat) - 168) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e364 M) (st fx' R' 0x8e384 M')
        /\ (forall x, In x KS_tpLi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV60l HV60r] G1 G2 G9 G18 G19 G20 G21 G23 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] K21.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PtpLi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpLi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpLi.kn0).
  { unfold know_ok, PtpLi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_nil. }
  destruct (PtpLi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpLi.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpLi.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpLi.ps0) with 0x8e384 in Hms. change (SR.ps_regs PtpLi.ps0) with (map (fun i => (i, nth i PtpLi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpLi.ps0) with PtpLi.cells0 in Hcells. unfold PtpLi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpLi.regs0 PtpLi.regs_out0 64 KS_tpLi KS_tpLi_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PtpLi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpLi.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpLd := LibSegY_tpLd.
Definition KS_tpLd : list nat := Eval vm_compute in (BG.kept_list 64 PtpLd.regs0 PtpLd.regs_out0).
Lemma KS_tpLd_ok : BG.kept_ok 64 PtpLd.regs0 PtpLd.regs_out0 KS_tpLd = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpLd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 288) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M ((V 2%nat) - 168) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = true -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 61%nat) -> 4096 <= (V 61%nat) <= 140737488355328 ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) (V 62%nat) -> 1 <= (V 62%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e364 M) (st fx' R' 0xb1048 M')
        /\ (forall x, In x KS_tpLd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582532
        /\ getr R' (reg 10) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 62%nat))).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV60l HV60r] [HV61l HV61r] [HV62l HV62r] G1 G2 G9 G18 G19 G20 G21 G23 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] K21 K22 [K23l K23r] K24 [K25l K25r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E PtpLd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpLd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpLd.kn0).
  { unfold know_ok, PtpLd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear - HV61l HV61r K23l K23r) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear - HV62l HV62r K25l K25r) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  destruct (PtpLd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpLd.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpLd.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpLd.ps0) with 0xb1048 in Hms. change (SR.ps_regs PtpLd.ps0) with (map (fun i => (i, nth i PtpLd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpLd.ps0) with PtpLd.cells0 in Hcells. unfold PtpLd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpLd.regs0 PtpLd.regs_out0 64 KS_tpLd KS_tpLd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpLd.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpLd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpLd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpLd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtpLd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpLd.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpMi := LibSegY_tpMi.
Definition KS_tpMi : list nat := Eval vm_compute in (BG.kept_list 64 PtpMi.regs0 PtpMi.regs_out0).
Lemma KS_tpMi_ok : BG.kept_ok 64 PtpMi.regs0 PtpMi.regs_out0 KS_tpMi = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpMi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 288) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e384 M) (st fx' R' 0x8e3a4 M')
        /\ (forall x, In x KS_tpMi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV60l HV60r] G1 G2 G9 G18 G19 G20 G21 G23 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] K21.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PtpMi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpMi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpMi.kn0).
  { unfold know_ok, PtpMi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_nil. }
  destruct (PtpMi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpMi.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpMi.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpMi.ps0) with 0x8e3a4 in Hms. change (SR.ps_regs PtpMi.ps0) with (map (fun i => (i, nth i PtpMi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpMi.ps0) with PtpMi.cells0 in Hcells. unfold PtpMi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpMi.regs0 PtpMi.regs_out0 64 KS_tpMi KS_tpMi_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PtpMi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpMi.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpMd := LibSegY_tpMd.
Definition KS_tpMd : list nat := Eval vm_compute in (BG.kept_list 64 PtpMd.regs0 PtpMd.regs_out0).
Lemma KS_tpMd_ok : BG.kept_ok 64 PtpMd.regs0 PtpMd.regs_out0 KS_tpMd = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpMd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 288) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M ((V 2%nat) - 136) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = true -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 61%nat) -> 4096 <= (V 61%nat) <= 140737488355328 ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) (V 62%nat) -> 1 <= (V 62%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e384 M) (st fx' R' 0xb1048 M')
        /\ (forall x, In x KS_tpMd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582564
        /\ getr R' (reg 10) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 62%nat))).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV60l HV60r] [HV61l HV61r] [HV62l HV62r] G1 G2 G9 G18 G19 G20 G21 G23 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] K21 K22 [K23l K23r] K24 [K25l K25r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E PtpMd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpMd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpMd.kn0).
  { unfold know_ok, PtpMd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear - HV61l HV61r K23l K23r) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear - HV62l HV62r K25l K25r) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  destruct (PtpMd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpMd.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpMd.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpMd.ps0) with 0xb1048 in Hms. change (SR.ps_regs PtpMd.ps0) with (map (fun i => (i, nth i PtpMd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpMd.ps0) with PtpMd.cells0 in Hcells. unfold PtpMd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpMd.regs0 PtpMd.regs_out0 64 KS_tpMd KS_tpMd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpMd.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpMd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpMd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpMd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtpMd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpMd.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpNi := LibSegY_tpNi.
Definition KS_tpNi : list nat := Eval vm_compute in (BG.kept_list 64 PtpNi.regs0 PtpNi.regs_out0).
Lemma KS_tpNi_ok : BG.kept_ok 64 PtpNi.regs0 PtpNi.regs_out0 KS_tpNi = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpNi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 288) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M ((V 40%nat) + 160) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e3a4 M) (st fx' R' 0x8e3c4 M')
        /\ (forall x, In x KS_tpNi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV60l HV60r] G1 G2 G9 G18 G19 G20 G21 G23 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] K21.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PtpNi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpNi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpNi.kn0).
  { unfold know_ok, PtpNi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_nil. }
  destruct (PtpNi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpNi.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpNi.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpNi.ps0) with 0x8e3c4 in Hms. change (SR.ps_regs PtpNi.ps0) with (map (fun i => (i, nth i PtpNi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpNi.ps0) with PtpNi.cells0 in Hcells. unfold PtpNi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpNi.regs0 PtpNi.regs_out0 64 KS_tpNi KS_tpNi_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PtpNi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpNi.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpNd := LibSegY_tpNd.
Definition KS_tpNd : list nat := Eval vm_compute in (BG.kept_list 64 PtpNd.regs0 PtpNd.regs_out0).
Lemma KS_tpNd_ok : BG.kept_ok 64 PtpNd.regs0 PtpNd.regs_out0 KS_tpNd = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpNd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 288) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M ((V 40%nat) + 160) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = true -> L5.u64_at RSEGS M ((V 40%nat) + 184) (V 61%nat) -> 4096 <= (V 61%nat) <= 140737488355328 ->
  L5.u64_at RSEGS M ((V 40%nat) + 176) (V 62%nat) -> 1 <= (V 62%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e3a4 M) (st fx' R' 0xb1048 M')
        /\ (forall x, In x KS_tpNd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582596
        /\ getr R' (reg 10) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 62%nat))).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV60l HV60r] [HV61l HV61r] [HV62l HV62r] G1 G2 G9 G18 G19 G20 G21 G23 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] K21 K22 [K23l K23r] K24 [K25l K25r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E PtpNd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpNd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpNd.kn0).
  { unfold know_ok, PtpNd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV61l HV61r K23l K23r) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV62l HV62r K25l K25r) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  destruct (PtpNd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpNd.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpNd.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpNd.ps0) with 0xb1048 in Hms. change (SR.ps_regs PtpNd.ps0) with (map (fun i => (i, nth i PtpNd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpNd.ps0) with PtpNd.cells0 in Hcells. unfold PtpNd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpNd.regs0 PtpNd.regs_out0 64 KS_tpNd KS_tpNd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpNd.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpNd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpNd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpNd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtpNd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpNd.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpN2 := LibSegY_tpN2.
Definition KS_tpN2 : list nat := Eval vm_compute in (BG.kept_list 64 PtpN2.regs0 PtpN2.regs_out0).
Lemma KS_tpN2_ok : BG.kept_ok 64 PtpN2.regs0 PtpN2.regs_out0 KS_tpN2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpN2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 288) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 40%nat) / 8) + 2147450900) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450900) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 40%nat) / 8) + 2147450900) <= i < (((V 40%nat) / 8) + 2147450900) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e3c4 M) (st fx' R' 0x8e3d8 M')
        /\ (forall x, In x KS_tpN2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 22) = Z_to_bv 64 18446744073709551608
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450903) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450902) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450901) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450900) 248).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] G1 G2 G9 G18 G19 G20 G21 G23 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PtpN2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpN2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpN2.kn0).
  { unfold know_ok, PtpN2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (PtpN2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpN2.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 40%nat) / 8) + 2147450900) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450900) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtpN2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpN2.ps0) with 0x8e3d8 in Hms. change (SR.ps_regs PtpN2.ps0) with (map (fun i => (i, nth i PtpN2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpN2.ps0) with PtpN2.cells0 in Hcells. unfold PtpN2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpN2.regs0 PtpN2.regs_out0 64 KS_tpN2 KS_tpN2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpN2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PtpN2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpOi := LibSegY_tpOi.
Definition KS_tpOi : list nat := Eval vm_compute in (BG.kept_list 64 PtpOi.regs0 PtpOi.regs_out0).
Lemma KS_tpOi_ok : BG.kept_ok 64 PtpOi.regs0 PtpOi.regs_out0 KS_tpOi = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpOi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 22) = Z_to_bv 64 18446744073709551608 -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 288) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M ((V 40%nat) + 96) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e3d8 M) (st fx' R' 0x8e3f8 M')
        /\ (forall x, In x KS_tpOi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV60l HV60r] G1 G2 G9 G18 G19 G20 G21 G22 G23 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] K21.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PtpOi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpOi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpOi.kn0).
  { unfold know_ok, PtpOi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_nil. }
  destruct (PtpOi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpOi.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpOi.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpOi.ps0) with 0x8e3f8 in Hms. change (SR.ps_regs PtpOi.ps0) with (map (fun i => (i, nth i PtpOi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpOi.ps0) with PtpOi.cells0 in Hcells. unfold PtpOi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpOi.regs0 PtpOi.regs_out0 64 KS_tpOi KS_tpOi_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PtpOi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpOi.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpOd := LibSegY_tpOd.
Definition KS_tpOd : list nat := Eval vm_compute in (BG.kept_list 64 PtpOd.regs0 PtpOd.regs_out0).
Lemma KS_tpOd_ok : BG.kept_ok 64 PtpOd.regs0 PtpOd.regs_out0 KS_tpOd = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpOd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 22) = Z_to_bv 64 18446744073709551608 -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 288) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M ((V 40%nat) + 96) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = true -> L5.u64_at RSEGS M ((V 40%nat) + 120) (V 61%nat) -> 4096 <= (V 61%nat) <= 140737488355328 ->
  L5.u64_at RSEGS M ((V 40%nat) + 112) (V 62%nat) -> 1 <= (V 62%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e3d8 M) (st fx' R' 0xb1048 M')
        /\ (forall x, In x KS_tpOd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582648
        /\ getr R' (reg 10) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (8 * (V 62%nat))).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV60l HV60r] [HV61l HV61r] [HV62l HV62r] G1 G2 G9 G18 G19 G20 G21 G22 G23 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] K21 K22 [K23l K23r] K24 [K25l K25r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E PtpOd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpOd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpOd.kn0).
  { unfold know_ok, PtpOd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV61l HV61r K23l K23r) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV62l HV62r K25l K25r) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_nil. }
  destruct (PtpOd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpOd.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpOd.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpOd.ps0) with 0xb1048 in Hms. change (SR.ps_regs PtpOd.ps0) with (map (fun i => (i, nth i PtpOd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpOd.ps0) with PtpOd.cells0 in Hcells. unfold PtpOd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpOd.regs0 PtpOd.regs_out0 64 KS_tpOd KS_tpOd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpOd.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpOd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpOd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpOd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtpOd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpOd.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpO2 := LibSegY_tpO2.
Definition KS_tpO2 : list nat := Eval vm_compute in (BG.kept_list 64 PtpO2.regs0 PtpO2.regs_out0).
Lemma KS_tpO2_ok : BG.kept_ok 64 PtpO2.regs0 PtpO2.regs_out0 KS_tpO2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpO2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 21) = Z_to_bv 64 ((V 40%nat) + 96) -> getr R (reg 22) = Z_to_bv 64 18446744073709551608 -> getr R (reg 23) = Z_to_bv 64 ((V 40%nat) + 160) -> getr R (reg 25) = Z_to_bv 64 ((V 40%nat) + 288) -> getr R (reg 26) = Z_to_bv 64 ((V 40%nat) + 224) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 40%nat) / 8) + 2147450892) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450892) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 40%nat) / 8) + 2147450892) <= i < (((V 40%nat) / 8) + 2147450892) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e3f8 M) (st fx' R' 0x8e408 M')
        /\ (forall x, In x KS_tpO2 -> getr R' (reg x) = getr R (reg x))
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450895) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450894) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450893) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450892) 248).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] G1 G2 G9 G18 G19 G20 G21 G22 G23 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PtpO2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpO2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpO2.kn0).
  { unfold know_ok, PtpO2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (PtpO2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpO2.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 40%nat) / 8) + 2147450892) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450892) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtpO2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpO2.ps0) with 0x8e408 in Hms. change (SR.ps_regs PtpO2.ps0) with (map (fun i => (i, nth i PtpO2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpO2.ps0) with PtpO2.cells0 in Hcells. unfold PtpO2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpO2.regs0 PtpO2.regs_out0 64 KS_tpO2 KS_tpO2_ok HR Hag Hregs j Hj). }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpPs := LibSegY_tpPs.
Definition KS_tpPs : list nat := Eval vm_compute in (BG.kept_list 64 PtpPs.regs0 PtpPs.regs_out0).
Lemma KS_tpPs_ok : BG.kept_ok 64 PtpPs.regs0 PtpPs.regs_out0 KS_tpPs = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpPs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M ((V 40%nat) + 32) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e408 M) (st fx' R' 0x8e424 M')
        /\ (forall x, In x KS_tpPs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV60l HV60r] G1 G2 G9 G18 G19 G20 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] K21.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PtpPs.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpPs.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpPs.kn0).
  { unfold know_ok, PtpPs.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_false (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_nil. }
  destruct (PtpPs.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpPs.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpPs.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpPs.ps0) with 0x8e424 in Hms. change (SR.ps_regs PtpPs.ps0) with (map (fun i => (i, nth i PtpPs.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpPs.ps0) with PtpPs.cells0 in Hcells. unfold PtpPs.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpPs.regs0 PtpPs.regs_out0 64 KS_tpPs KS_tpPs_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PtpPs.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpPs.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpPl := LibSegY_tpPl.
Definition KS_tpPl : list nat := Eval vm_compute in (BG.kept_list 64 PtpPl.regs0 PtpPl.regs_out0).
Lemma KS_tpPl_ok : BG.kept_ok 64 PtpPl.regs0 PtpPl.regs_out0 KS_tpPl = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpPl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> L5.u8_at RSEGS M ((V 40%nat) + 32) (V 60%nat) ->
  0 <= (V 60%nat) <= 255 -> Z.testbit (V 60%nat) 0 = true ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e408 M) (st fx' R' 0x8e414 M')
        /\ (forall x, In x KS_tpPl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 1).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV60l HV60r] G1 G2 G9 G18 G19 G20 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 [K20l K20r] K21.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 60%nat => Z_to_bv 64 (V 60%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 60%nat => (V 60%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PtpPl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpPl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpPl.kn0).
  { unfold know_ok, PtpPl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | byte_tac ltac:(clear - HV60l HV60r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV60l HV60r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_true (V 60%nat) ltac:(clear - HV60l HV60r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_nil. }
  destruct (PtpPl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpPl.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpPl.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpPl.ps0) with 0x8e414 in Hms. change (SR.ps_regs PtpPl.ps0) with (map (fun i => (i, nth i PtpPl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpPl.ps0) with PtpPl.cells0 in Hcells. unfold PtpPl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpPl.regs0 PtpPl.regs_out0 64 KS_tpPl KS_tpPl_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PtpPl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpPl.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpPl2 := LibSegY_tpPl2.
Definition KS_tpPl2 : list nat := Eval vm_compute in (BG.kept_list 64 PtpPl2.regs0 PtpPl2.regs_out0).
Lemma KS_tpPl2_ok : BG.kept_ok 64 PtpPl2.regs0 PtpPl2.regs_out0 KS_tpPl2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpPl2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> L5.u64_at RSEGS M ((V 40%nat) + 32) (V 62%nat) ->
  L5.u64_at RSEGS M ((V 40%nat) + 48) (V 61%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e414 M) (st fx' R' 0xb1048 M')
        /\ (forall x, In x KS_tpPl2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582692
        /\ getr R' (reg 10) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (2 * ((V 62%nat) / 2))).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] [HV61l HV61r] [HV62l HV62r] G1 G2 G9 G18 G19 G20 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 K20.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | 61%nat => Z_to_bv 64 (V 61%nat) | 62%nat => Z_to_bv 64 (V 62%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | 61%nat => (V 61%nat) | 62%nat => (V 62%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E PtpPl2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpPl2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpPl2.kn0).
  { unfold know_ok, PtpPl2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | clear - HV41l HV41r K13l K13r K15 K16 K18; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | clear - HV40l HV40r K6l K6r K10 K16 K17; lia | exactA K20]. }
    apply Forall_nil. }
  destruct (PtpPl2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpPl2.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpPl2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpPl2.ps0) with 0xb1048 in Hms. change (SR.ps_regs PtpPl2.ps0) with (map (fun i => (i, nth i PtpPl2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpPl2.ps0) with PtpPl2.cells0 in Hcells. unfold PtpPl2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpPl2.regs0 PtpPl2.regs_out0 64 KS_tpPl2 KS_tpPl2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpPl2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpPl2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpPl2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpPl2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtpPl2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpPl2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpQ1 := LibSegY_tpQ1.
Definition KS_tpQ1 : list nat := Eval vm_compute in (BG.kept_list 64 PtpQ1.regs0 PtpQ1.regs_out0).
Lemma KS_tpQ1_ok : BG.kept_ok 64 PtpQ1.regs0 PtpQ1.regs_out0 KS_tpQ1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpQ1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> 4096 <= (V 40%nat) <= 140737488354816 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 ->
  L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) -> (65536 + 6438912 <= (V 40%nat) \/ (V 40%nat) + 512 <= 65536) ->
  (65536 + 6438912 <= (V 41%nat) \/ (V 41%nat) + 1 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 8) -> ~ ((((V 40%nat) / 8) + 2147450884) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450884) + 3) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 8) -> ~ ((((V 40%nat) / 8) + 2147450884) <= i < (((V 40%nat) / 8) + 2147450884) + 3) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e424 M) (st fx' R' 0x61fcc M')
        /\ (forall x, In x KS_tpQ1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582736
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 64
        /\ L5.u64_at RSEGS M' (V 40%nat) 1172321806
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450884) 248
        /\ L5.defined M' ((V 40%nat) + 8) 504).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV58l HV58r] G1 G2 G9 G18 G19 G20 G27 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 K20.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PtpQ1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpQ1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpQ1.kn0).
  { unfold know_ok, PtpQ1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | clear - HV2l HV2r K0l K0r K17 K18; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18 K20; lia | clear - HV41l HV41r K13l K13r K15 K16 K18 K20; lia | clear - HV41l HV41r K13l K13r K15 K16 K18 K20; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (PtpQ1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpQ1.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 8) -> ~ ((((V 40%nat) / 8) + 2147450884) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450884) + 3) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PtpQ1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpQ1.ps0) with 0x61fcc in Hms. change (SR.ps_regs PtpQ1.ps0) with (map (fun i => (i, nth i PtpQ1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpQ1.ps0) with PtpQ1.cells0 in Hcells. unfold PtpQ1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpQ1.regs0 PtpQ1.regs_out0 64 KS_tpQ1 KS_tpQ1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpQ1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpQ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpQ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpQ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpQt := LibSegY_tpQt.
Definition KS_tpQt : list nat := Eval vm_compute in (BG.kept_list 64 PtpQt.regs0 PtpQt.regs_out0).
Lemma KS_tpQt_ok : BG.kept_ok 64 PtpQt.regs0 PtpQt.regs_out0 KS_tpQt = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpQt_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 860160 884736 -> L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M 885800 837440 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x61fcc M) (st fx' R' 0xcc740 M')
        /\ (forall x, In x KS_tpQt -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 6) = Z_to_bv 64 837440
        /\ getr R' (reg 11) = Z_to_bv 64 245
        /\ getr R' (reg 12) = getr R (reg 11)).
Proof.
  intros [HV2l HV2r] G2 K0 K1 K2 K3.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PtpQt.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpQt.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpQt.kn0).
  { unfold know_ok, PtpQt.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K3]. }
    apply Forall_nil. }
  destruct (PtpQt.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpQt.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtpQt.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpQt.ps0) with 0xcc740 in Hms. change (SR.ps_regs PtpQt.ps0) with (map (fun i => (i, nth i PtpQt.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpQt.ps0) with PtpQt.cells0 in Hcells. unfold PtpQt.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpQt.regs0 PtpQt.regs_out0 64 KS_tpQt KS_tpQt_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpQt.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PtpQt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQt.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtpQt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtpQt.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtpQt.regs_out0]. rewrite (BG.edenot_kept 64 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpQ20 := LibSegY_tpQ20.
Definition KS_tpQ20 : list nat := Eval vm_compute in (BG.kept_list 64 PtpQ20.regs0 PtpQ20.regs_out0).
Lemma KS_tpQ20_ok : BG.kept_ok 64 PtpQ20.regs0 PtpQ20.regs_out0 KS_tpQ20 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpQ20_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 51%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 54%nat) -> 4096 <= (V 40%nat) <= 140737488354816 ->
  aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) ->
  L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 192 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 192 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e450 M) (st fx' R' 0x8e52c M')
        /\ (forall x, In x KS_tpQ20 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 54%nat)
        /\ L5.u8_at RSEGS M' (V 41%nat) 0).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] [HV52l HV52r] [HV53l HV53r] [HV54l HV54r] [HV58l HV58r] G1 G2 G8 G9 G18 G19 G20 G27 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 [K26l K26r] K27 K28 K29 K30 K31.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | 54%nat => (V 54%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PtpQ20.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpQ20.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpQ20.kn0).
  { unfold know_ok, PtpQ20.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K26l K26r K28 K29 K31; lia | clear - HV41l HV41r K26l K26r K28 K29 K31; lia | clear - HV41l HV41r K26l K26r K28 K29 K31; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (PtpQ20.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpQ20.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtpQ20.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | evalEk' ZA Hag ltac:(clear) | clear - HV41l HV41r K26l K26r K28 K29 K31 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpQ20.ps0) with 0x8e52c in Hms. change (SR.ps_regs PtpQ20.ps0) with (map (fun i => (i, nth i PtpQ20.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpQ20.ps0) with PtpQ20.cells0 in Hcells. unfold PtpQ20.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpQ20.regs0 PtpQ20.regs_out0 64 KS_tpQ20 KS_tpQ20_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpQ20.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpQ20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ20.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PtpQ20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ20.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PtpQ20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ20.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PtpQ20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ20.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpQ20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ20.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PtpQ20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ20.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PtpQ20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ20.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PtpQ20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ20.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PtpQ20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ20.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PtpQ20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ20.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PtpQ20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ20.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PtpQ20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ20.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PtpQ20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ20.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PtpQ20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ20.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PtpQ20.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtpQ216 := LibSegY_tpQ216.
Definition KS_tpQ216 : list nat := Eval vm_compute in (BG.kept_list 64 PtpQ216.regs0 PtpQ216.regs_out0).
Lemma KS_tpQ216_ok : BG.kept_ok 64 PtpQ216.regs0 PtpQ216.regs_out0 KS_tpQ216 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tpQ216_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 58%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) + 16) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 18) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 40%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 40%nat) + 32) -> getr R (reg 27) = Z_to_bv 64 (V 40%nat) ->
  140735332487424 <= (V 2%nat) <= 140737488355312 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 192) 208 -> L5.img_clear M 860160 884736 ->
  L5.u64_at RSEGS M 911160 2147450880 -> L5.u32_at RSEGS M 911168 1 -> L5.u64_at RSEGS M ((V 2%nat) + 8) (V 42%nat) -> L5.u64_at RSEGS M (V 2%nat) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 54%nat) -> 4096 <= (V 40%nat) <= 140737488354816 ->
  aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 512 -> L5.writable RSEGS M (V 40%nat) 512 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 512 <= 2147446784) ->
  L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 64 -> L5.u64_at RSEGS M ((V 40%nat) + 504) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 512 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 192) + 208 <= (V 40%nat) \/ (V 40%nat) + 512 <= ((V 2%nat) - 192)) -> (((V 2%nat) - 192) + 208 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 192)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e450 M) (st fx' R' 0x8e52c M')
        /\ (forall x, In x KS_tpQ216 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 16)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 54%nat)
        /\ L5.u8_at RSEGS M' (V 41%nat) 0).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] [HV52l HV52r] [HV53l HV53r] [HV54l HV54r] [HV58l HV58r] G1 G2 G8 G9 G18 G19 G20 G27 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 [K19l K19r] K20 K21 K22 K23 K24 K25 [K26l K26r] K27 K28 K29 K30 K31.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | 54%nat => (V 54%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PtpQ216.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtpQ216.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtpQ216.kn0).
  { unfold know_ok, PtpQ216.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K30 K31; lia | clear - HV2l HV2r K0l K0r K30 K31; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | clear - HV40l HV40r K19l K19r K23 K29 K30; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K26l K26r K28 K29 K31; lia | clear - HV41l HV41r K26l K26r K28 K29 K31; lia | clear - HV41l HV41r K26l K26r K28 K29 K31; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r K23 K29 K30) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K30 K31) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (PtpQ216.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PtpQ216.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtpQ216.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | evalEk' ZA Hag ltac:(clear) | clear - HV41l HV41r K26l K26r K28 K29 K31 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtpQ216.ps0) with 0x8e52c in Hms. change (SR.ps_regs PtpQ216.ps0) with (map (fun i => (i, nth i PtpQ216.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtpQ216.ps0) with PtpQ216.cells0 in Hcells. unfold PtpQ216.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtpQ216.regs0 PtpQ216.regs_out0 64 KS_tpQ216 KS_tpQ216_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtpQ216.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtpQ216.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ216.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PtpQ216.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ216.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PtpQ216.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ216.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PtpQ216.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ216.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtpQ216.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ216.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PtpQ216.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ216.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PtpQ216.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ216.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PtpQ216.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ216.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PtpQ216.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ216.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PtpQ216.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ216.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PtpQ216.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ216.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PtpQ216.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ216.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PtpQ216.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ216.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PtpQ216.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtpQ216.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PtpQ216.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV41l HV41r K26l K26r K28 K29 K31) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End L5ATP2.
