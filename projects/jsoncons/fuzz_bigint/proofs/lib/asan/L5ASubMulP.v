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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegZ_vsmA LibSegZ_vsmI LibSegZ_vsmIL LibSegZ_vsmB LibSegZ_vsmJ LibSegZ_vsmJL LibSegZ_vsmT LibSegZ_vsmK.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia.
Local Ltac nodj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac nodisj := L5FastLia.prune_arith; repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac lia := first [ solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ] | solve [ nodisj; L5FastLia.lia_st ] | L5FastLia.plia ].   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5ASMP.
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
Module PvsmA := LibSegZ_vsmA.
Definition KS_vsmA : list nat := Eval vm_compute in (BG.kept_list 56 PvsmA.regs0 PvsmA.regs_out0).
Lemma KS_vsmA_ok : BG.kept_ok 56 PvsmA.regs0 PvsmA.regs_out0 KS_vsmA = true. Proof. vm_compute. reflexivity. Qed.
Lemma vsmA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 (V 35%nat) -> getr R (reg 14) = Z_to_bv 64 (V 36%nat) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488351232 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + ((8 * (V 35%nat)) + 8) <= 2147446784) -> L5.defined M (V 33%nat) ((8 * (V 35%nat)) + 8) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) ((V 35%nat) + 1) -> (((V 2%nat) - 80) + 80 <= (V 33%nat) \/ (V 33%nat) + ((8 * (V 35%nat)) + 8) <= ((V 2%nat) - 80)) ->
  ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 33%nat) / 8) + 2147450880) \/ (((V 33%nat) / 8) + 2147450880) + ((V 35%nat) + 1) <= (V 33%nat)) -> L5.writable RSEGS M (V 33%nat) ((8 * (V 35%nat)) + 8) -> 4096 <= (V 34%nat) <= 140737488351232 -> aligned (V 34%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= 2147446784) -> L5.defined M (V 34%nat) (8 * (V 35%nat)) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) (V 35%nat) -> (((V 2%nat) - 80) + 80 <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= ((V 2%nat) - 80)) ->
  ((V 34%nat) + (8 * (V 35%nat)) <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 34%nat)) -> 4096 <= (V 36%nat) <= 140737488355320 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 8 <= 2147446784) ->
  L5.defined M (V 36%nat) 8 -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 8 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 8 <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + 1 <= (V 36%nat)) ->
  L5.writable RSEGS M (V 36%nat) 8 -> 1 <= (V 35%nat) <= 300 -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= (V 33%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (V 36%nat) \/ (V 36%nat) + 8 <= (V 33%nat)) ->
  ((V 34%nat) + (8 * (V 35%nat)) <= (V 36%nat) \/ (V 36%nat) + 8 <= (V 34%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 33%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + 1 <= (V 33%nat)) -> ((V 36%nat) + 8 <= (((V 33%nat) / 8) + 2147450880) \/ (((V 33%nat) / 8) + 2147450880) + ((V 35%nat) + 1) <= (V 36%nat)) ->
  ((V 36%nat) + 8 <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x935d8 M) (st fx' R' 0x93658 M')
        /\ (forall x, In x KS_vsmA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 5) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 6) = Z_to_bv 64 4294967295
        /\ getr R' (reg 7) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 2147450880
        /\ getr R' (reg 17) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880)
        /\ getr R' (reg 28) = Z_to_bv 64 (((V 34%nat) / 8) + 2147450880)
        /\ getr R' (reg 29) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 30) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 31) = Z_to_bv 64 0
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
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV56l HV56r] G2 G11 G12 G13 G14 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 [K14l K14r] K15 K16 K17 K18 K19 K20 [K21l K21r] K22 K23 K24 K25 K26 K27 K28 [K29l K29r] K30 K31 K32 K33 K34 K35 K36.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 56%nat => (V 56%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PvsmA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvsmA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvsmA.kn0).
  { unfold know_ok, PvsmA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K24]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K36; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (PvsmA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvsmA.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvsmA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K19 K26 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvsmA.ps0) with 0x93658 in Hms. change (SR.ps_regs PvsmA.ps0) with (map (fun i => (i, nth i PvsmA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvsmA.ps0) with PvsmA.cells0 in Hcells. unfold PvsmA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvsmA.regs0 PvsmA.regs_out0 56 KS_vsmA KS_vsmA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvsmA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvsmA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmA.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PvsmA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmA.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PvsmA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmA.regs_out0 E' R' 7 Hregs) by (clear; lia). cbn [nth PvsmA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvsmA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmA.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvsmA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmA.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PvsmA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmA.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PvsmA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmA.regs_out0 E' R' 28 Hregs) by (clear; lia). cbn [nth PvsmA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmA.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth PvsmA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmA.regs_out0 E' R' 30 Hregs) by (clear; lia). cbn [nth PvsmA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmA.regs_out0 E' R' 31 Hregs) by (clear; lia). cbn [nth PvsmA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvsmI := LibSegZ_vsmI.
Definition KS_vsmI : list nat := Eval vm_compute in (BG.kept_list 56 PvsmI.regs0 PvsmI.regs_out0).
Lemma KS_vsmI_ok : BG.kept_ok 56 PvsmI.regs0 PvsmI.regs_out0 KS_vsmI = true. Proof. vm_compute. reflexivity. Qed.
Lemma vsmI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 5) = Z_to_bv 64 (((V 33%nat) + (8 * (V 37%nat))) + 8) -> getr R (reg 6) = Z_to_bv 64 4294967295 -> getr R (reg 7) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 34%nat) + (8 * (V 37%nat))) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 (V 35%nat) -> getr R (reg 14) = Z_to_bv 64 (V 36%nat) -> getr R (reg 15) = Z_to_bv 64 ((V 33%nat) + (8 * (V 37%nat))) -> getr R (reg 16) = Z_to_bv 64 2147450880 -> getr R (reg 17) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) -> getr R (reg 28) = Z_to_bv 64 (((V 37%nat) + ((V 34%nat) / 8)) + 2147450880) -> getr R (reg 29) = Z_to_bv 64 ((V 34%nat) + (8 * (V 37%nat))) -> getr R (reg 30) = Z_to_bv 64 (V 40%nat) -> getr R (reg 31) = Z_to_bv 64 (V 38%nat) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488351232 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + ((8 * (V 35%nat)) + 8) <= 2147446784) -> L5.defined M (V 33%nat) ((8 * (V 35%nat)) + 8) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) ((V 35%nat) + 1) -> (((V 2%nat) - 80) + 80 <= (V 33%nat) \/ (V 33%nat) + ((8 * (V 35%nat)) + 8) <= ((V 2%nat) - 80)) ->
  ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 33%nat) / 8) + 2147450880) \/ (((V 33%nat) / 8) + 2147450880) + ((V 35%nat) + 1) <= (V 33%nat)) -> L5.writable RSEGS M (V 33%nat) ((8 * (V 35%nat)) + 8) -> 4096 <= (V 34%nat) <= 140737488351232 -> aligned (V 34%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= 2147446784) -> L5.defined M (V 34%nat) (8 * (V 35%nat)) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) (V 35%nat) -> (((V 2%nat) - 80) + 80 <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= ((V 2%nat) - 80)) ->
  ((V 34%nat) + (8 * (V 35%nat)) <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 34%nat)) -> 4096 <= (V 36%nat) <= 140737488355320 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 8 <= 2147446784) ->
  L5.defined M (V 36%nat) 8 -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 8 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 8 <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + 1 <= (V 36%nat)) ->
  L5.writable RSEGS M (V 36%nat) 8 -> 1 <= (V 35%nat) <= 300 -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= (V 33%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (V 36%nat) \/ (V 36%nat) + 8 <= (V 33%nat)) ->
  ((V 34%nat) + (8 * (V 35%nat)) <= (V 36%nat) \/ (V 36%nat) + 8 <= (V 34%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 33%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + 1 <= (V 33%nat)) -> ((V 36%nat) + 8 <= (((V 33%nat) / 8) + 2147450880) \/ (((V 33%nat) / 8) + 2147450880) + ((V 35%nat) + 1) <= (V 36%nat)) ->
  ((V 36%nat) + 8 <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 36%nat)) -> 0 <= (V 37%nat) <= 299 -> 2 <= ((V 35%nat) - (V 37%nat)) <= 300 -> 2 <= (V 40%nat) <= 300 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 33%nat) + (8 * (V 37%nat))) + 0) <= bv_unsigned a < (((V 33%nat) + (8 * (V 37%nat))) + 0) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 33%nat) + (8 * (V 37%nat))) + 0) <= i < (((V 33%nat) + (8 * (V 37%nat))) + 0) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93658 M) (st fx' R' 0x93658 M')
        /\ (forall x, In x KS_vsmI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 (((V 33%nat) + (8 * (V 37%nat))) + 16)
        /\ getr R' (reg 9) = Z_to_bv 64 (((V 33%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 34%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 15) = Z_to_bv 64 (((V 33%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 24) = Z_to_bv 64 0
        /\ getr R' (reg 28) = Z_to_bv 64 (((V 37%nat) + ((V 34%nat) / 8)) + 2147450881)
        /\ getr R' (reg 29) = Z_to_bv 64 (((V 34%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 30) = Z_to_bv 64 ((V 40%nat) - 1)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] [HV56l HV56r] [HV57l HV57r] [HV58l HV58r] G2 G5 G6 G7 G8 G10 G11 G12 G13 G14 G15 G16 G17 G28 G29 G30 G31 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 [K14l K14r] K15 K16 K17 K18 K19 K20 [K21l K21r] K22 K23 K24 K25 K26 K27 K28 [K29l K29r] K30 K31 K32 K33 K34 K35 K36 [K37l K37r] [K38l K38r] [K39l K39r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 56%nat => (V 56%nat) | 57%nat => (V 57%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PvsmI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvsmI.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvsmI.kn0).
  { unfold know_ok, PvsmI.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K24]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K37l K37r K38l K38r; nodj) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r HV37l HV37r K37l K37r; nodj) | exact (conj K38l K38r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K39l K39r; nodj) | exact (conj K39l K39r)]. }
    apply Forall_nil. }
  destruct (PvsmI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvsmI.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 33%nat) + (8 * (V 37%nat))) + 0) <= bv_unsigned a < (((V 33%nat) + (8 * (V 37%nat))) + 0) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvsmI.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV37l HV37r K37l K37r K38l K38r; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV37l HV37r K37l K37r K38l K38r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvsmI.ps0) with 0x93658 in Hms. change (SR.ps_regs PvsmI.ps0) with (map (fun i => (i, nth i PvsmI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvsmI.ps0) with PvsmI.cells0 in Hcells. unfold PvsmI.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvsmI.regs0 PvsmI.regs_out0 56 KS_vsmI KS_vsmI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvsmI.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PvsmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmI.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvsmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmI.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvsmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmI.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvsmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmI.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PvsmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmI.regs_out0 E' R' 28 Hregs) by (clear; lia). cbn [nth PvsmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmI.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth PvsmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvsmI.regs_out0 E' R' 30 Hregs) by (clear; lia). cbn [nth PvsmI.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvsmIL := LibSegZ_vsmIL.
Definition KS_vsmIL : list nat := Eval vm_compute in (BG.kept_list 56 PvsmIL.regs0 PvsmIL.regs_out0).
Lemma KS_vsmIL_ok : BG.kept_ok 56 PvsmIL.regs0 PvsmIL.regs_out0 KS_vsmIL = true. Proof. vm_compute. reflexivity. Qed.
Lemma vsmIL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 5) = Z_to_bv 64 (((V 33%nat) + (8 * (V 37%nat))) + 8) -> getr R (reg 6) = Z_to_bv 64 4294967295 -> getr R (reg 7) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 34%nat) + (8 * (V 37%nat))) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 (V 35%nat) -> getr R (reg 14) = Z_to_bv 64 (V 36%nat) -> getr R (reg 15) = Z_to_bv 64 ((V 33%nat) + (8 * (V 37%nat))) -> getr R (reg 16) = Z_to_bv 64 2147450880 -> getr R (reg 17) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) -> getr R (reg 28) = Z_to_bv 64 (((V 37%nat) + ((V 34%nat) / 8)) + 2147450880) -> getr R (reg 29) = Z_to_bv 64 ((V 34%nat) + (8 * (V 37%nat))) -> getr R (reg 30) = Z_to_bv 64 (V 40%nat) -> getr R (reg 31) = Z_to_bv 64 (V 38%nat) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488351232 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + ((8 * (V 35%nat)) + 8) <= 2147446784) -> L5.defined M (V 33%nat) ((8 * (V 35%nat)) + 8) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) ((V 35%nat) + 1) -> (((V 2%nat) - 80) + 80 <= (V 33%nat) \/ (V 33%nat) + ((8 * (V 35%nat)) + 8) <= ((V 2%nat) - 80)) ->
  ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 33%nat) / 8) + 2147450880) \/ (((V 33%nat) / 8) + 2147450880) + ((V 35%nat) + 1) <= (V 33%nat)) -> L5.writable RSEGS M (V 33%nat) ((8 * (V 35%nat)) + 8) -> 4096 <= (V 34%nat) <= 140737488351232 -> aligned (V 34%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= 2147446784) -> L5.defined M (V 34%nat) (8 * (V 35%nat)) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) (V 35%nat) -> (((V 2%nat) - 80) + 80 <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= ((V 2%nat) - 80)) ->
  ((V 34%nat) + (8 * (V 35%nat)) <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 34%nat)) -> 4096 <= (V 36%nat) <= 140737488355320 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 8 <= 2147446784) ->
  L5.defined M (V 36%nat) 8 -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 8 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 8 <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + 1 <= (V 36%nat)) ->
  L5.writable RSEGS M (V 36%nat) 8 -> 1 <= (V 35%nat) <= 300 -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= (V 33%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (V 36%nat) \/ (V 36%nat) + 8 <= (V 33%nat)) ->
  ((V 34%nat) + (8 * (V 35%nat)) <= (V 36%nat) \/ (V 36%nat) + 8 <= (V 34%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 33%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + 1 <= (V 33%nat)) -> ((V 36%nat) + 8 <= (((V 33%nat) / 8) + 2147450880) \/ (((V 33%nat) / 8) + 2147450880) + ((V 35%nat) + 1) <= (V 36%nat)) ->
  ((V 36%nat) + 8 <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 36%nat)) -> 0 <= (V 37%nat) <= 299 -> 1 <= ((V 35%nat) - (V 37%nat)) <= 1 -> 1 <= (V 40%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 33%nat) + (8 * (V 37%nat))) + 0) <= bv_unsigned a < (((V 33%nat) + (8 * (V 37%nat))) + 0) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 33%nat) + (8 * (V 37%nat))) + 0) <= i < (((V 33%nat) + (8 * (V 37%nat))) + 0) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93658 M) (st fx' R' 0x93728 M')
        /\ (forall x, In x KS_vsmIL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 (((V 33%nat) + (8 * (V 37%nat))) + 16)
        /\ getr R' (reg 9) = Z_to_bv 64 (((V 33%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 34%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 15) = Z_to_bv 64 (((V 33%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 24) = Z_to_bv 64 0
        /\ getr R' (reg 28) = Z_to_bv 64 (((V 37%nat) + ((V 34%nat) / 8)) + 2147450881)
        /\ getr R' (reg 29) = Z_to_bv 64 (((V 34%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 30) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] [HV56l HV56r] [HV57l HV57r] [HV58l HV58r] G2 G5 G6 G7 G8 G10 G11 G12 G13 G14 G15 G16 G17 G28 G29 G30 G31 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 [K14l K14r] K15 K16 K17 K18 K19 K20 [K21l K21r] K22 K23 K24 K25 K26 K27 K28 [K29l K29r] K30 K31 K32 K33 K34 K35 K36 [K37l K37r] [K38l K38r] [K39l K39r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | 58%nat => Z_to_bv 64 (V 58%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 56%nat => (V 56%nat) | 57%nat => (V 57%nat) | 58%nat => (V 58%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PvsmIL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvsmIL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvsmIL.kn0).
  { unfold know_ok, PvsmIL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K24]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K37l K37r K38l K38r; nodj) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r HV37l HV37r K37l K37r; nodj) | exact (conj K38l K38r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K39l K39r; nodj) | exact (conj K39l K39r)]. }
    apply Forall_nil. }
  destruct (PvsmIL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvsmIL.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 33%nat) + (8 * (V 37%nat))) + 0) <= bv_unsigned a < (((V 33%nat) + (8 * (V 37%nat))) + 0) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvsmIL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV37l HV37r K37l K37r K38l K38r; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV37l HV37r K37l K37r K38l K38r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvsmIL.ps0) with 0x93728 in Hms. change (SR.ps_regs PvsmIL.ps0) with (map (fun i => (i, nth i PvsmIL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvsmIL.ps0) with PvsmIL.cells0 in Hcells. unfold PvsmIL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvsmIL.regs0 PvsmIL.regs_out0 56 KS_vsmIL KS_vsmIL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvsmIL.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PvsmIL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmIL.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvsmIL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmIL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvsmIL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmIL.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvsmIL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmIL.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PvsmIL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmIL.regs_out0 E' R' 28 Hregs) by (clear; lia). cbn [nth PvsmIL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmIL.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth PvsmIL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvsmIL.regs_out0 E' R' 30 Hregs) by (clear; lia). cbn [nth PvsmIL.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvsmB := LibSegZ_vsmB.
Definition KS_vsmB : list nat := Eval vm_compute in (BG.kept_list 56 PvsmB.regs0 PvsmB.regs_out0).
Lemma KS_vsmB_ok : BG.kept_ok 56 PvsmB.regs0 PvsmB.regs_out0 KS_vsmB = true. Proof. vm_compute. reflexivity. Qed.
Lemma vsmB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 7) = Z_to_bv 64 (((V 36%nat) / 8) + 2147450880) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) -> getr R (reg 13) = Z_to_bv 64 (V 35%nat) -> getr R (reg 14) = Z_to_bv 64 (V 36%nat) -> getr R (reg 16) = Z_to_bv 64 2147450880 -> getr R (reg 17) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488351232 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + ((8 * (V 35%nat)) + 8) <= 2147446784) -> L5.defined M (V 33%nat) ((8 * (V 35%nat)) + 8) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) ((V 35%nat) + 1) -> (((V 2%nat) - 80) + 80 <= (V 33%nat) \/ (V 33%nat) + ((8 * (V 35%nat)) + 8) <= ((V 2%nat) - 80)) ->
  ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 33%nat) / 8) + 2147450880) \/ (((V 33%nat) / 8) + 2147450880) + ((V 35%nat) + 1) <= (V 33%nat)) -> L5.writable RSEGS M (V 33%nat) ((8 * (V 35%nat)) + 8) -> 4096 <= (V 34%nat) <= 140737488351232 -> aligned (V 34%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= 2147446784) -> L5.defined M (V 34%nat) (8 * (V 35%nat)) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) (V 35%nat) -> (((V 2%nat) - 80) + 80 <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= ((V 2%nat) - 80)) ->
  ((V 34%nat) + (8 * (V 35%nat)) <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 34%nat)) -> 4096 <= (V 36%nat) <= 140737488355320 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 8 <= 2147446784) ->
  L5.defined M (V 36%nat) 8 -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 8 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 8 <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + 1 <= (V 36%nat)) ->
  L5.writable RSEGS M (V 36%nat) 8 -> 1 <= (V 35%nat) <= 300 -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= (V 33%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (V 36%nat) \/ (V 36%nat) + 8 <= (V 33%nat)) ->
  ((V 34%nat) + (8 * (V 35%nat)) <= (V 36%nat) \/ (V 36%nat) + 8 <= (V 34%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 33%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + 1 <= (V 33%nat)) -> ((V 36%nat) + 8 <= (((V 33%nat) / 8) + 2147450880) \/ (((V 33%nat) / 8) + 2147450880) + ((V 35%nat) + 1) <= (V 36%nat)) ->
  ((V 36%nat) + 8 <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 0) <= i < ((V 36%nat) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x9372c M) (st fx' R' 0x93754 M')
        /\ (forall x, In x KS_vsmB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 6) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] G2 G7 G11 G12 G13 G14 G16 G17 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 [K14l K14r] K15 K16 K17 K18 K19 K20 [K21l K21r] K22 K23 K24 K25 K26 K27 K28 [K29l K29r] K30 K31 K32 K33 K34 K35 K36.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvsmB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvsmB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvsmB.kn0).
  { unfold know_ok, PvsmB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K24]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K36; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (PvsmB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvsmB.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvsmB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvsmB.ps0) with 0x93754 in Hms. change (SR.ps_regs PvsmB.ps0) with (map (fun i => (i, nth i PvsmB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvsmB.ps0) with PvsmB.cells0 in Hcells. unfold PvsmB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvsmB.regs0 PvsmB.regs_out0 56 KS_vsmB KS_vsmB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvsmB.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PvsmB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmB.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PvsmB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvsmB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvsmB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvsmB.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvsmB.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvsmJ := LibSegZ_vsmJ.
Definition KS_vsmJ : list nat := Eval vm_compute in (BG.kept_list 56 PvsmJ.regs0 PvsmJ.regs_out0).
Lemma KS_vsmJ_ok : BG.kept_ok 56 PvsmJ.regs0 PvsmJ.regs_out0 KS_vsmJ = true. Proof. vm_compute. reflexivity. Qed.
Lemma vsmJ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 5) = Z_to_bv 64 ((V 33%nat) + (8 * (V 37%nat))) -> getr R (reg 6) = Z_to_bv 64 (V 40%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 33%nat) + (8 * (V 37%nat))) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 34%nat) + (8 * (V 37%nat))) -> getr R (reg 13) = Z_to_bv 64 (V 35%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 34%nat) + (8 * (V 37%nat))) -> getr R (reg 15) = Z_to_bv 64 (V 38%nat) -> getr R (reg 16) = Z_to_bv 64 2147450880 -> getr R (reg 17) = Z_to_bv 64 (((V 37%nat) + ((V 33%nat) / 8)) + 2147450880) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488351232 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + ((8 * (V 35%nat)) + 8) <= 2147446784) -> L5.defined M (V 33%nat) ((8 * (V 35%nat)) + 8) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) ((V 35%nat) + 1) -> (((V 2%nat) - 80) + 80 <= (V 33%nat) \/ (V 33%nat) + ((8 * (V 35%nat)) + 8) <= ((V 2%nat) - 80)) ->
  ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 33%nat) / 8) + 2147450880) \/ (((V 33%nat) / 8) + 2147450880) + ((V 35%nat) + 1) <= (V 33%nat)) -> L5.writable RSEGS M (V 33%nat) ((8 * (V 35%nat)) + 8) -> 4096 <= (V 34%nat) <= 140737488351232 -> aligned (V 34%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= 2147446784) -> L5.defined M (V 34%nat) (8 * (V 35%nat)) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) (V 35%nat) -> (((V 2%nat) - 80) + 80 <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= ((V 2%nat) - 80)) ->
  ((V 34%nat) + (8 * (V 35%nat)) <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 34%nat)) -> 4096 <= (V 36%nat) <= 140737488355320 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 8 <= 2147446784) ->
  L5.defined M (V 36%nat) 8 -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 8 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 8 <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + 1 <= (V 36%nat)) ->
  L5.writable RSEGS M (V 36%nat) 8 -> 1 <= (V 35%nat) <= 300 -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= (V 33%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (V 36%nat) \/ (V 36%nat) + 8 <= (V 33%nat)) ->
  ((V 34%nat) + (8 * (V 35%nat)) <= (V 36%nat) \/ (V 36%nat) + 8 <= (V 34%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 33%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + 1 <= (V 33%nat)) -> ((V 36%nat) + 8 <= (((V 33%nat) / 8) + 2147450880) \/ (((V 33%nat) / 8) + 2147450880) + ((V 35%nat) + 1) <= (V 36%nat)) ->
  ((V 36%nat) + 8 <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 36%nat)) -> 0 <= (V 37%nat) <= 299 -> 2 <= ((V 35%nat) - (V 37%nat)) <= 300 -> 2 <= (V 40%nat) <= 300 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 33%nat) + (8 * (V 37%nat))) + 0) <= bv_unsigned a < (((V 33%nat) + (8 * (V 37%nat))) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 33%nat) + (8 * (V 37%nat))) + 0) <= i < (((V 33%nat) + (8 * (V 37%nat))) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93754 M) (st fx' R' 0x93754 M')
        /\ (forall x, In x KS_vsmJ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 (((V 33%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 6) = Z_to_bv 64 ((V 40%nat) - 1)
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 33%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 34%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 34%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 17) = Z_to_bv 64 (((V 37%nat) + ((V 33%nat) / 8)) + 2147450881)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV40l HV40r] [HV56l HV56r] [HV57l HV57r] G2 G5 G6 G10 G11 G12 G13 G14 G15 G16 G17 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 [K14l K14r] K15 K16 K17 K18 K19 K20 [K21l K21r] K22 K23 K24 K25 K26 K27 K28 [K29l K29r] K30 K31 K32 K33 K34 K35 K36 [K37l K37r] [K38l K38r] [K39l K39r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 40%nat => (V 40%nat) | 56%nat => (V 56%nat) | 57%nat => (V 57%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PvsmJ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvsmJ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvsmJ.kn0).
  { unfold know_ok, PvsmJ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K24]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K37l K37r K38l K38r; nodj) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r HV37l HV37r K37l K37r; nodj) | exact (conj K38l K38r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K39l K39r; nodj) | exact (conj K39l K39r)]. }
    apply Forall_nil. }
  destruct (PvsmJ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvsmJ.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 33%nat) + (8 * (V 37%nat))) + 0) <= bv_unsigned a < (((V 33%nat) + (8 * (V 37%nat))) + 0) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvsmJ.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV37l HV37r K37l K37r K38l K38r; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV37l HV37r K37l K37r K38l K38r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvsmJ.ps0) with 0x93754 in Hms. change (SR.ps_regs PvsmJ.ps0) with (map (fun i => (i, nth i PvsmJ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvsmJ.ps0) with PvsmJ.cells0 in Hcells. unfold PvsmJ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvsmJ.regs0 PvsmJ.regs_out0 56 KS_vsmJ KS_vsmJ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvsmJ.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PvsmJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmJ.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PvsmJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmJ.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvsmJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmJ.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvsmJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmJ.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvsmJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvsmJ.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PvsmJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvsmJL := LibSegZ_vsmJL.
Definition KS_vsmJL : list nat := Eval vm_compute in (BG.kept_list 56 PvsmJL.regs0 PvsmJL.regs_out0).
Lemma KS_vsmJL_ok : BG.kept_ok 56 PvsmJL.regs0 PvsmJL.regs_out0 KS_vsmJL = true. Proof. vm_compute. reflexivity. Qed.
Lemma vsmJL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 5) = Z_to_bv 64 ((V 33%nat) + (8 * (V 37%nat))) -> getr R (reg 6) = Z_to_bv 64 (V 40%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 33%nat) + (8 * (V 37%nat))) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 12) = Z_to_bv 64 ((V 34%nat) + (8 * (V 37%nat))) -> getr R (reg 13) = Z_to_bv 64 (V 35%nat) -> getr R (reg 14) = Z_to_bv 64 ((V 34%nat) + (8 * (V 37%nat))) -> getr R (reg 15) = Z_to_bv 64 (V 38%nat) -> getr R (reg 16) = Z_to_bv 64 2147450880 -> getr R (reg 17) = Z_to_bv 64 (((V 37%nat) + ((V 33%nat) / 8)) + 2147450880) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488351232 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + ((8 * (V 35%nat)) + 8) <= 2147446784) -> L5.defined M (V 33%nat) ((8 * (V 35%nat)) + 8) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) ((V 35%nat) + 1) -> (((V 2%nat) - 80) + 80 <= (V 33%nat) \/ (V 33%nat) + ((8 * (V 35%nat)) + 8) <= ((V 2%nat) - 80)) ->
  ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 33%nat) / 8) + 2147450880) \/ (((V 33%nat) / 8) + 2147450880) + ((V 35%nat) + 1) <= (V 33%nat)) -> L5.writable RSEGS M (V 33%nat) ((8 * (V 35%nat)) + 8) -> 4096 <= (V 34%nat) <= 140737488351232 -> aligned (V 34%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= 2147446784) -> L5.defined M (V 34%nat) (8 * (V 35%nat)) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) (V 35%nat) -> (((V 2%nat) - 80) + 80 <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= ((V 2%nat) - 80)) ->
  ((V 34%nat) + (8 * (V 35%nat)) <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 34%nat)) -> 4096 <= (V 36%nat) <= 140737488355320 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 8 <= 2147446784) ->
  L5.defined M (V 36%nat) 8 -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 8 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 8 <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + 1 <= (V 36%nat)) ->
  L5.writable RSEGS M (V 36%nat) 8 -> 1 <= (V 35%nat) <= 300 -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= (V 33%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (V 36%nat) \/ (V 36%nat) + 8 <= (V 33%nat)) ->
  ((V 34%nat) + (8 * (V 35%nat)) <= (V 36%nat) \/ (V 36%nat) + 8 <= (V 34%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 33%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + 1 <= (V 33%nat)) -> ((V 36%nat) + 8 <= (((V 33%nat) / 8) + 2147450880) \/ (((V 33%nat) / 8) + 2147450880) + ((V 35%nat) + 1) <= (V 36%nat)) ->
  ((V 36%nat) + 8 <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 36%nat)) -> 0 <= (V 37%nat) <= 299 -> 1 <= ((V 35%nat) - (V 37%nat)) <= 1 -> 1 <= (V 40%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 33%nat) + (8 * (V 37%nat))) + 0) <= bv_unsigned a < (((V 33%nat) + (8 * (V 37%nat))) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 33%nat) + (8 * (V 37%nat))) + 0) <= i < (((V 33%nat) + (8 * (V 37%nat))) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93754 M) (st fx' R' 0x937a8 M')
        /\ (forall x, In x KS_vsmJL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 (((V 33%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 6) = Z_to_bv 64 0
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 33%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 12) = Z_to_bv 64 (((V 34%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 34%nat) + (8 * (V 37%nat))) + 8)
        /\ getr R' (reg 17) = Z_to_bv 64 (((V 37%nat) + ((V 33%nat) / 8)) + 2147450881)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV40l HV40r] [HV56l HV56r] [HV57l HV57r] G2 G5 G6 G10 G11 G12 G13 G14 G15 G16 G17 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 [K14l K14r] K15 K16 K17 K18 K19 K20 [K21l K21r] K22 K23 K24 K25 K26 K27 K28 [K29l K29r] K30 K31 K32 K33 K34 K35 K36 [K37l K37r] [K38l K38r] [K39l K39r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 56%nat => Z_to_bv 64 (V 56%nat) | 57%nat => Z_to_bv 64 (V 57%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 40%nat => (V 40%nat) | 56%nat => (V 56%nat) | 57%nat => (V 57%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PvsmJL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvsmJL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvsmJL.kn0).
  { unfold know_ok, PvsmJL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 K38l K38r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35 K38l K38r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K24]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r; nodj) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K37l K37r K38l K38r; nodj) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36 K38l K38r HV37l HV37r K37l K37r; nodj) | exact (conj K38l K38r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K39l K39r; nodj) | exact (conj K39l K39r)]. }
    apply Forall_nil. }
  destruct (PvsmJL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvsmJL.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 33%nat) + (8 * (V 37%nat))) + 0) <= bv_unsigned a < (((V 33%nat) + (8 * (V 37%nat))) + 0) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvsmJL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV37l HV37r K37l K37r K38l K38r; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV37l HV37r K37l K37r K38l K38r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvsmJL.ps0) with 0x937a8 in Hms. change (SR.ps_regs PvsmJL.ps0) with (map (fun i => (i, nth i PvsmJL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvsmJL.ps0) with PvsmJL.cells0 in Hcells. unfold PvsmJL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvsmJL.regs0 PvsmJL.regs_out0 56 KS_vsmJL KS_vsmJL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvsmJL.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PvsmJL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmJL.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PvsmJL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmJL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvsmJL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmJL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvsmJL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmJL.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvsmJL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvsmJL.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PvsmJL.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvsmT := LibSegZ_vsmT.
Definition KS_vsmT : list nat := Eval vm_compute in (BG.kept_list 56 PvsmT.regs0 PvsmT.regs_out0).
Lemma KS_vsmT_ok : BG.kept_ok 56 PvsmT.regs0 PvsmT.regs_out0 KS_vsmT = true. Proof. vm_compute. reflexivity. Qed.
Lemma vsmT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 13) = Z_to_bv 64 (V 35%nat) -> getr R (reg 16) = Z_to_bv 64 2147450880 ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488351232 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + ((8 * (V 35%nat)) + 8) <= 2147446784) -> L5.defined M (V 33%nat) ((8 * (V 35%nat)) + 8) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) ((V 35%nat) + 1) -> (((V 2%nat) - 80) + 80 <= (V 33%nat) \/ (V 33%nat) + ((8 * (V 35%nat)) + 8) <= ((V 2%nat) - 80)) ->
  ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 33%nat) / 8) + 2147450880) \/ (((V 33%nat) / 8) + 2147450880) + ((V 35%nat) + 1) <= (V 33%nat)) -> L5.writable RSEGS M (V 33%nat) ((8 * (V 35%nat)) + 8) -> 4096 <= (V 34%nat) <= 140737488351232 -> aligned (V 34%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= 2147446784) -> L5.defined M (V 34%nat) (8 * (V 35%nat)) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) (V 35%nat) -> (((V 2%nat) - 80) + 80 <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= ((V 2%nat) - 80)) ->
  ((V 34%nat) + (8 * (V 35%nat)) <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 34%nat)) -> 4096 <= (V 36%nat) <= 140737488355320 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 8 <= 2147446784) ->
  L5.defined M (V 36%nat) 8 -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 8 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 8 <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + 1 <= (V 36%nat)) ->
  L5.writable RSEGS M (V 36%nat) 8 -> 1 <= (V 35%nat) <= 300 -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (V 34%nat) \/ (V 34%nat) + (8 * (V 35%nat)) <= (V 33%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (V 36%nat) \/ (V 36%nat) + 8 <= (V 33%nat)) ->
  ((V 34%nat) + (8 * (V 35%nat)) <= (V 36%nat) \/ (V 36%nat) + 8 <= (V 34%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 33%nat)) -> ((V 33%nat) + ((8 * (V 35%nat)) + 8) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + 1 <= (V 33%nat)) -> ((V 36%nat) + 8 <= (((V 33%nat) / 8) + 2147450880) \/ (((V 33%nat) / 8) + 2147450880) + ((V 35%nat) + 1) <= (V 36%nat)) ->
  ((V 36%nat) + 8 <= (((V 34%nat) / 8) + 2147450880) \/ (((V 34%nat) / 8) + 2147450880) + (V 35%nat) <= (V 36%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 50%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 33%nat) + (8 * (V 35%nat))) + 0) <= bv_unsigned a < (((V 33%nat) + (8 * (V 35%nat))) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 33%nat) + (8 * (V 35%nat))) + 0) <= i < (((V 33%nat) + (8 * (V 35%nat))) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x937a8 M) (st fx' R' 0x937f0 M')
        /\ (forall x, In x KS_vsmT -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + (8 * (V 35%nat)))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + (8 * (V 35%nat))) 0
        /\ L5.defined M' (((V 33%nat) + (8 * (V 35%nat))) + 8) 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] G2 G11 G13 G16 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 K13 [K14l K14r] K15 K16 K17 K18 K19 K20 [K21l K21r] K22 K23 K24 K25 K26 K27 K28 [K29l K29r] K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PvsmT.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvsmT.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvsmT.kn0).
  { unfold know_ok, PvsmT.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36 HV35l HV35r K8 K11 K12 K29l K29r K31 K34 K35; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K24]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K23 K26 K27 K31 K32 K34 K35 K36; nodj) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r K16 K19 K20 K30 K32 K33 K36; nodj) | evalEk ZA ltac:(clear - HV35l HV35r K8 K11 K12 K16 K19 K20 K29l K29r K30 K31 K32 K33 K34 K35 K36; nodj) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear - HV41l HV41r; nodj) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear - HV42l HV42r; nodj) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear - HV43l HV43r; nodj) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear - HV44l HV44r; nodj) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear - HV45l HV45r; nodj) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear - HV46l HV46r; nodj) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear - HV47l HV47r; nodj) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear - HV48l HV48r; nodj) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear - HV49l HV49r; nodj) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K19 K26; nodj) | evalEk ZA ltac:(clear - HV50l HV50r; nodj) | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | clear - HV2l HV2r K0l K0r K11 K19 K26; lia | exactA K46]. }
    apply Forall_nil. }
  destruct (PvsmT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvsmT.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 33%nat) + (8 * (V 35%nat))) + 0) <= bv_unsigned a < (((V 33%nat) + (8 * (V 35%nat))) + 0) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvsmT.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; nodj) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvsmT.ps0) with 0x937f0 in Hms. change (SR.ps_regs PvsmT.ps0) with (map (fun i => (i, nth i PvsmT.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvsmT.ps0) with PvsmT.cells0 in Hcells. unfold PvsmT.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvsmT.regs0 PvsmT.regs_out0 56 KS_vsmT KS_vsmT_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvsmT.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvsmT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmT.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvsmT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmT.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvsmT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmT.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvsmT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmT.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvsmT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmT.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvsmT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmT.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvsmT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmT.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PvsmT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmT.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PvsmT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmT.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PvsmT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmT.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PvsmT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmT.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PvsmT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmT.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PvsmT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K12 K30 K31 K33 K34 K35 HV35l HV35r K16 K19 K20 K29l K29r K32 K36; nodj) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvsmK := LibSegZ_vsmK.
Definition KS_vsmK : list nat := Eval vm_compute in (BG.kept_list 56 PvsmK.regs0 PvsmK.regs_out0).
Lemma KS_vsmK_ok : BG.kept_ok 56 PvsmK.regs0 PvsmK.regs_out0 KS_vsmK = true. Proof. vm_compute. reflexivity. Qed.
Lemma vsmK_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) ->
  140735332487248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 50%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x937c4 M) (st fx' R' 0x937f0 M')
        /\ (forall x, In x KS_vsmK -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 50%nat)).
Proof.
  intros [HV2l HV2r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] G2 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PvsmK.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvsmK.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvsmK.kn0).
  { unfold know_ok, PvsmK.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r; nodj) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r; nodj) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r; nodj) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r; nodj) | evalEk ZA ltac:(clear - HV41l HV41r; nodj) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r; nodj) | evalEk ZA ltac:(clear - HV42l HV42r; nodj) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r; nodj) | evalEk ZA ltac:(clear - HV43l HV43r; nodj) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r; nodj) | evalEk ZA ltac:(clear - HV44l HV44r; nodj) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r; nodj) | evalEk ZA ltac:(clear - HV45l HV45r; nodj) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r; nodj) | evalEk ZA ltac:(clear - HV46l HV46r; nodj) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r; nodj) | evalEk ZA ltac:(clear - HV47l HV47r; nodj) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r; nodj) | evalEk ZA ltac:(clear - HV48l HV48r; nodj) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r; nodj) | evalEk ZA ltac:(clear - HV49l HV49r; nodj) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r; nodj) | evalEk ZA ltac:(clear - HV50l HV50r; nodj) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K12]. }
    apply Forall_nil. }
  destruct (PvsmK.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvsmK.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvsmK.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvsmK.ps0) with 0x937f0 in Hms. change (SR.ps_regs PvsmK.ps0) with (map (fun i => (i, nth i PvsmK.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvsmK.ps0) with PvsmK.cells0 in Hcells. unfold PvsmK.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvsmK.regs0 PvsmK.regs_out0 56 KS_vsmK KS_vsmK_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvsmK.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvsmK.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmK.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvsmK.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmK.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvsmK.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmK.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvsmK.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmK.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvsmK.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmK.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PvsmK.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmK.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PvsmK.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmK.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PvsmK.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmK.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PvsmK.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvsmK.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PvsmK.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvsmK.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PvsmK.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End L5ASMP.
