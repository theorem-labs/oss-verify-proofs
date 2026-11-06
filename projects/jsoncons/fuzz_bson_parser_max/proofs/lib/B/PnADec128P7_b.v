(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BigLinkZA.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan. From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b. From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_adkX1_b LibSegBa_adkXI_b LibSegBa_adkXJ_b LibSegBa_adkXT_b LibSegBa_adkXN_b LibSegBa_adkXO_b LibSegBa_adkXU_b LibSegBa_adkXC_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADP7.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).

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
(* [comment removed for export] *)
Lemma u8x2_of_KWord2a E M b off e a v a' v0 v1 : kentry_ok RSEGS E M (KWord (SA b off) 2 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> v0 = v mod 256 -> v1 = (v / 256) mod 256 ->
  L5.u8_at RSEGS M a' v0 /\ L5.u8_at RSEGS M (a' + 1) v1.
Proof.
  intros K Ha Hv -> -> ->. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd).
  rewrite L5K.adenot_e, Ha in Rd. rewrite (BG.word_of_unsigned _ _ Hv) in Rd.
  pose proof (bv_unsigned_in_range 64 (edenot E e)) as Rg. rewrite Hv in Rg. change (bv_modulus 64) with (2 ^ 64) in Rg.
  unfold word_to_le_bytes in Rd. rewrite Z_to_bv_unsigned in Rd. unfold bv_wrap in Rd. change (bv_modulus 64) with (2 ^ 64) in Rd.
  rewrite (Z.mod_small v (2 ^ 64)) in Rd by (clear - Rg; lia). cbn [Z_to_le_bytes rdn] in Rd. unfold L5.u8_at.
  assert (E1 : (Z_to_bv 64 (a + off) + 1 = Z_to_bv 64 (a + off + 1))%bv).
  { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    change (bv_unsigned (1 : bv 64)) with 1. apply Z.add_mod_idemp_l. clear; lia. }
  rewrite E1 in Rd.
  destruct (match M (Z_to_bv 64 (a + off)) with Some b0 => Some b0 | None => seg_rom RSEGS (Z_to_bv 64 (a + off)) end) as [x|] eqn:X; [|discriminate].
  destruct (match M (Z_to_bv 64 (a + off + 1)) with Some b0 => Some b0 | None => seg_rom RSEGS (Z_to_bv 64 (a + off + 1)) end) as [y|] eqn:Y; [|discriminate].
  injection Rd as Ex Ey. split.
  - cbn [rdn]. rewrite X. subst x. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mod_mod by (clear; lia). reflexivity.
  - cbn [rdn]. rewrite Y. subst y. f_equal. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.shiftr_div_pow2 by (clear; lia). change (2 ^ 8) with 256. rewrite Z.mod_mod by (clear; lia). reflexivity.
Qed.
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
(* [comment removed for export] *)
Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
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
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
(* [comment removed for export] *)
Module PadkX1 := LibSegBa_adkX1_b.
Definition KS_adkX1_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkX1.regs0 PadkX1.regs_out0).
Lemma KS_adkX1_0_ok : BG.kept_ok 80 PadkX1.regs0 PadkX1.regs_out0 KS_adkX1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkX1_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkX1.regs0 PadkX1.regs_out1).
Lemma KS_adkX1_1_ok : BG.kept_ok 80 PadkX1.regs0 PadkX1.regs_out1 KS_adkX1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkX1_2 : list nat := Eval vm_compute in (BG.kept_list 80 PadkX1.regs0 PadkX1.regs_out2).
Lemma KS_adkX1_2_ok : BG.kept_ok 80 PadkX1.regs0 PadkX1.regs_out2 KS_adkX1_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkX1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 11) = Z_to_bv 64 (V 36%nat) -> getr R (reg 13) = Z_to_bv 64 (V 39%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 30) = Z_to_bv 64 ((V 33%nat) + (V 44%nat)) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 44%nat) <= 1 -> 0 <= (V 39%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb4994 M) (st fx' R' 0xb49d8 M')
        /\ (forall x, In x KS_adkX1_0 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 12)) = (((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488)
        /\ getr R' (reg 14) = Z_to_bv 64 31
        /\ (((((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488) - 31) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb4994 M) (st fx' R' 0xb49ac M')
        /\ (forall x, In x KS_adkX1_1 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 12)) = (((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488)
        /\ getr R' (reg 14) = Z_to_bv 64 30
        /\ (((((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488) - 30) mod 2 ^ 64) < 1
        /\ 1 <= (((((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488) - 31) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb4994 M) (st fx' R' 0xb4a04 M')
        /\ (forall x, In x KS_adkX1_2 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 12)) = (((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488)
        /\ getr R' (reg 14) = Z_to_bv 64 30
        /\ 1 <= (((((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488) - 30) mod 2 ^ 64)
        /\ 1 <= (((((8589934592 * (V 39%nat)) mod 2 ^ 64) / 576460752303423488) - 31) mod 2 ^ 64))).
Proof.
  intros w2 w33 w35 w36 w39 w44 w50 x2 x8 x9 x10 x11 x13 x18 x19 x20 x23 x26 x27 x30
    sp_in sp_al sp_wr fr_in fi_in sg_in hi_in.
  pose (Vz := fun j : nat => match j with
    | 2%nat => V 2%nat | 33%nat => V 33%nat | 35%nat => V 35%nat | 36%nat => V 36%nat
    | 39%nat => V 39%nat | 44%nat => V 44%nat | 50%nat => V 50%nat
    | _ => bv_unsigned (getr R (reg j)) end).
  pose (E := Env (fun j : nat => match j with
    | 2%nat | 33%nat | 35%nat | 36%nat | 39%nat | 44%nat | 50%nat => Z_to_bv 64 (Vz j)
    | _ => getr R (reg j) end) (fun _ => [])).
  assert (vals : forall j, bv_unsigned (ev E j) = Vz j).
  { intros j. unfold E, Vz. cbn [ev].
    do 51 (destruct j as [|j]; [cbn beta iota; first [apply BG.unsigned_lit; assumption | reflexivity] |]).
    reflexivity. }
  assert (know0 : know_ok RSEGS E M PadkX1.kn0).
  { unfold know_ok, PadkX1.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    - apply L5K.kentry_KRange with (v := V 2%nat); [evalEk vals idtac | exact sp_in].
    - apply L5K.kentry_KAlign with (v := V 2%nat); [evalEk vals idtac | lia | exact sp_al].
    - apply L5K.kentry_KWr with (a := V 2%nat) (n := 256); [evalEk vals idtac | evalEk vals idtac | lia | lia | lia | exactA sp_wr].
    - apply L5K.kentry_KRange with (v := V 50%nat); [evalEk vals idtac | exact fr_in].
    - apply L5K.kentry_KRange with (v := V 33%nat); [evalEk vals idtac | exact fi_in].
    - apply L5K.kentry_KRange with (v := V 44%nat); [evalEk vals idtac | exact sg_in].
    - apply L5K.kentry_KRange with (v := V 39%nat); [evalEk vals idtac | exact hi_in]. }
  assert (slots0 : regs_ok E PadkX1.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. unfold PadkX1.regs0. cbn [tl BG.slots].
    repeat apply conj; first [exact I | slotP vals]. }
  destruct (PadkX1.seg_sound_ax fx E R M slots0 know0 ltac:(constructor))
    as (fxo & Eo & Ro & Mo & k & ps & pick & agr & run & outs & r0 & rgn & frame & cells & grow).
  pose (top := (8589934592 * V 39%nat) mod 2 ^ 64 / 576460752303423488).
  pose (e12 := EAlu ALU_SRL (EMd M_MUL (ELit 8589934592) (EVar 39)) (ELit 59)).
  assert (h39 : bv_unsigned (ev Eo 39) = V 39%nat).
  { rewrite <- (proj1 agr 39%nat) by (unfold PadkX1.NX0; lia). exact (vals 39%nat). }
  assert (t12 : bv_unsigned (edenot Eo e12) = top).
  { unfold e12. cbn [edenot]. rewrite u_srl64, u_mul64, h39, !BG.unsigned_lit by lia. reflexivity. }
  assert (dip : forall c lo hi, 0 <= c < 2 ^ 64 ->
      kentry_ok RSEGS Eo Mo (KRange (EAlu ALU_SLTU (EAlu ALU_SUB e12 (ELit c)) (ELit 1)) lo hi) ->
      lo <= (if (top - c) mod 2 ^ 64 <? 1 then 1 else 0) <= hi).
  { intros c lo hi cw cell. apply (L5K.range_of_KRange _ _ _ _ _ _ _ cell).
    cbn [edenot]. cbn [edenot] in t12. rewrite u_sltu64, u_sub64, t12, !BG.unsigned_lit by lia. reflexivity. }
  assert (same : forall a, Mo a = M a) by (intros a; apply frame; apply L5K.outside_nil_e).
  exists fxo, Ro, Mo.
  refine (conj grow (conj same (conj (fun i _ => same (Z_to_bv 64 i)) _))).
  apply nth_error_In in pick.
  replace PadkX1.PSS with [PadkX1.ps0; PadkX1.ps1; PadkX1.ps2] in pick by (vm_compute; reflexivity).
  assert (r12 : forall ro, (forall i e, In (i, e) (map (fun j => (j, nth j ro (ELit 0))) (seq 1 31)) ->
      (0 < i < 32)%nat /\ getr Ro (reg i) = edenot Eo e) -> nth 12 ro (ELit 0) = e12 ->
      bv_unsigned (getr Ro (reg 12)) = top).
  { intros ro rs n12. rewrite (BG.out_reg ro Eo Ro 12 rs), n12 by lia. exact t12. }
  destruct pick as [<-|[<-|[<-|[]]]].
  - left.
    assert (in31 : In (KRange (EAlu ALU_SLTU (EAlu ALU_SUB e12 (ELit 31)) (ELit 1)) 1 1) (SR.ps_cells PadkX1.ps0))
      by (vm_compute; left; reflexivity).
    pose proof (dip 31 1 1 ltac:(lia) (cells _ in31)) as d31.
    split; [exact run|]. split; [exact (BG.kept_regs E Eo R Ro PadkX1.regs0 PadkX1.regs_out0 80 KS_adkX1_0 KS_adkX1_0_ok slots0 agr outs)|].
    split; [exact (r12 _ outs eq_refl)|].
    split. { rewrite (BG.out_reg PadkX1.regs_out0 Eo Ro 14 outs) by lia. L5K.norm_expr. reflexivity. }
    destruct ((top - 31) mod 2 ^ 64 <? 1) eqn:b31; [apply Z.ltb_lt in b31; exact b31 | lia].
  - right; left.
    assert (in30 : In (KRange (EAlu ALU_SLTU (EAlu ALU_SUB e12 (ELit 30)) (ELit 1)) 1 1) (SR.ps_cells PadkX1.ps1))
      by (vm_compute; left; reflexivity).
    assert (in31 : In (KRange (EAlu ALU_SLTU (EAlu ALU_SUB e12 (ELit 31)) (ELit 1)) 0 0) (SR.ps_cells PadkX1.ps1))
      by (vm_compute; right; left; reflexivity).
    pose proof (dip 30 1 1 ltac:(lia) (cells _ in30)) as d30.
    pose proof (dip 31 0 0 ltac:(lia) (cells _ in31)) as d31.
    split; [exact run|]. split; [exact (BG.kept_regs E Eo R Ro PadkX1.regs0 PadkX1.regs_out1 80 KS_adkX1_1 KS_adkX1_1_ok slots0 agr outs)|].
    split; [exact (r12 _ outs eq_refl)|].
    split. { rewrite (BG.out_reg PadkX1.regs_out1 Eo Ro 14 outs) by lia. L5K.norm_expr. reflexivity. }
    destruct ((top - 31) mod 2 ^ 64 <? 1) eqn:b31; [lia|apply Z.ltb_ge in b31].
    destruct ((top - 30) mod 2 ^ 64 <? 1) eqn:b30; [apply Z.ltb_lt in b30|lia].
    split; assumption.
  - right; right.
    assert (in30 : In (KRange (EAlu ALU_SLTU (EAlu ALU_SUB e12 (ELit 30)) (ELit 1)) 0 0) (SR.ps_cells PadkX1.ps2))
      by (vm_compute; left; reflexivity).
    assert (in31 : In (KRange (EAlu ALU_SLTU (EAlu ALU_SUB e12 (ELit 31)) (ELit 1)) 0 0) (SR.ps_cells PadkX1.ps2))
      by (vm_compute; right; left; reflexivity).
    pose proof (dip 30 0 0 ltac:(lia) (cells _ in30)) as d30.
    pose proof (dip 31 0 0 ltac:(lia) (cells _ in31)) as d31.
    split; [exact run|]. split; [exact (BG.kept_regs E Eo R Ro PadkX1.regs0 PadkX1.regs_out2 80 KS_adkX1_2 KS_adkX1_2_ok slots0 agr outs)|].
    split; [exact (r12 _ outs eq_refl)|].
    split. { rewrite (BG.out_reg PadkX1.regs_out2 Eo Ro 14 outs) by lia. L5K.norm_expr. reflexivity. }
    destruct ((top - 30) mod 2 ^ 64 <? 1) eqn:b30; [lia|apply Z.ltb_ge in b30].
    destruct ((top - 31) mod 2 ^ 64 <? 1) eqn:b31; [lia|apply Z.ltb_ge in b31].
    split; assumption.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkXI := LibSegBa_adkXI_b.
Definition KS_adkXI : list nat := Eval vm_compute in (BG.kept_list 80 PadkXI.regs0 PadkXI.regs_out0).
Lemma KS_adkXI_ok : BG.kept_ok 80 PadkXI.regs0 PadkXI.regs_out0 KS_adkXI = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkXI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 30) = Z_to_bv 64 ((V 33%nat) + (V 44%nat)) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 44%nat) <= 1 -> L5.u8_at RSEGS M 6759112 16 -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 42) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb49ac M) (st fx' R' 0x77c94 M')
        /\ (forall x, In x KS_adkXI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 739916
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + (V 44%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 6759113
        /\ getr R' (reg 12) = Z_to_bv 64 8
        /\ getr R' (reg 18) = Z_to_bv 64 6759112
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 33%nat) + (V 44%nat))
        /\ getr R' (reg 22) = getr R (reg 22)).
Proof.
  intros w2 w33 w44 w50 x2 x8 x9 x18 x19 x20 x23 x26 x27 x30 sp_in sp_al sp_wr fr_in fi_in sg_in ch16 sl176.
  pose (Vz := fun j : nat => match j with
    | 2%nat => V 2%nat | 33%nat => V 33%nat | 44%nat => V 44%nat | 50%nat => V 50%nat
    | _ => bv_unsigned (getr R (reg j)) end).
  pose (E := Env (fun j : nat => match j with
    | 2%nat | 33%nat | 44%nat | 50%nat => Z_to_bv 64 (Vz j)
    | _ => getr R (reg j) end) (fun _ => [])).
  assert (vals : forall j, bv_unsigned (ev E j) = Vz j).
  { intros j. unfold E, Vz. cbn [ev].
    do 51 (destruct j as [|j]; [cbn beta iota; first [apply BG.unsigned_lit; assumption | reflexivity] |]).
    reflexivity. }
  assert (know0 : know_ok RSEGS E M PadkXI.kn0).
  { unfold know_ok, PadkXI.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    - apply L5K.kentry_KRange with (v := V 2%nat); [evalEk vals idtac | exact sp_in].
    - apply L5K.kentry_KAlign with (v := V 2%nat); [evalEk vals idtac | lia | exact sp_al].
    - apply L5K.kentry_KWr with (a := V 2%nat) (n := 256); [evalEk vals idtac | evalEk vals idtac | lia | lia | lia | exactA sp_wr].
    - apply L5K.kentry_KRange with (v := V 50%nat); [evalEk vals idtac | exact fr_in].
    - apply L5K.kentry_KRange with (v := V 33%nat); [evalEk vals idtac | exact fi_in].
    - apply L5K.kentry_KRange with (v := V 44%nat); [evalEk vals idtac | exact sg_in].
    - apply L5K.kentry_KWord1 with (a := 0) (v := 16); [evalEk vals idtac | evalEk vals idtac | lia | lia | lia | exactA ch16].
    - apply L5K.kentry_KWord8 with (a := V 2%nat) (v := V 33%nat + 42); [evalEk vals idtac | evalEk vals idtac | lia | lia | exactA sl176]. }
  assert (slots0 : regs_ok E PadkXI.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. unfold PadkXI.regs0. cbn [tl BG.slots].
    repeat apply conj; first [exact I | slotP vals]. }
  destruct (PadkXI.seg_sound_ax fx E R M slots0 know0 ltac:(constructor))
    as (fxo & Eo & Ro & Mo & k & ps & pick & agr & run & outs & r0 & rgn & frame & cells & grow).
  apply nth_error_In in pick.
  replace PadkXI.PSS with [PadkXI.ps0] in pick by (vm_compute; reflexivity).
  destruct pick as [<-|[]].
  pose proof (BG.kept_regs E Eo R Ro PadkXI.regs0 PadkXI.regs_out0 80 KS_adkXI KS_adkXI_ok slots0 agr outs) as keep.
  assert (o1 : getr Ro (reg 1) = Z_to_bv 64 739916).
  { rewrite (BG.out_reg PadkXI.regs_out0 Eo Ro 1 outs) by lia. L5K.norm_expr. reflexivity. }
  assert (o10 : getr Ro (reg 10) = Z_to_bv 64 (V 33%nat + V 44%nat)).
  { rewrite (BG.out_reg PadkXI.regs_out0 Eo Ro 10 outs) by lia. L5K.norm_expr. wordP' vals agr. }
  assert (o11 : getr Ro (reg 11) = Z_to_bv 64 6759113).
  { rewrite (BG.out_reg PadkXI.regs_out0 Eo Ro 11 outs) by lia. L5K.norm_expr. reflexivity. }
  assert (o12 : getr Ro (reg 12) = Z_to_bv 64 8).
  { rewrite (BG.out_reg PadkXI.regs_out0 Eo Ro 12 outs) by lia. L5K.norm_expr. reflexivity. }
  assert (o18 : getr Ro (reg 18) = Z_to_bv 64 6759112).
  { rewrite (BG.out_reg PadkXI.regs_out0 Eo Ro 18 outs) by lia. L5K.norm_expr. reflexivity. }
  assert (o20 : getr Ro (reg 20) = Z_to_bv 64 (V 33%nat + V 44%nat)).
  { rewrite (BG.out_reg PadkXI.regs_out0 Eo Ro 20 outs) by lia. L5K.norm_expr. wordP' vals agr. }
  assert (o22 : getr Ro (reg 22) = getr R (reg 22)) by (apply keep; apply L5K.in_b; vm_compute; reflexivity).
  assert (same : forall a, Mo a = M a) by (intros a; apply frame; apply L5K.outside_nil_e).
  exists fxo, Ro, Mo.
  refine (conj grow (conj same (conj (fun i _ => same (Z_to_bv 64 i)) (conj run (conj keep _))))).
  repeat split; assumption.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkXJ := LibSegBa_adkXJ_b.
Definition KS_adkXJ : list nat := Eval vm_compute in (BG.kept_list 80 PadkXJ.regs0 PadkXJ.regs_out0).
Lemma KS_adkXJ_ok : BG.kept_ok 80 PadkXJ.regs0 PadkXJ.regs_out0 KS_adkXJ = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkXJ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 6759112 -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + (V 44%nat)) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 44%nat) <= 1 -> L5.u8_at RSEGS M 6759112 16 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb4a4c M) (st fx' R' 0xb4a90 M')
        /\ (forall x, In x KS_adkXJ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 16
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 21) = getr R (reg 21)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 33%nat) + (V 44%nat)) + 8)).
Proof.
  intros w2 w33 w44 w50 x2 x8 x9 x18 x19 x20 x23 x26 x27 sp_in sp_al sp_wr fr_in fi_in sg_in ch16.
  pose (Vz := fun j : nat => match j with
    | 2%nat => V 2%nat | 33%nat => V 33%nat | 44%nat => V 44%nat | 50%nat => V 50%nat
    | _ => bv_unsigned (getr R (reg j)) end).
  pose (E := Env (fun j : nat => match j with
    | 2%nat | 33%nat | 44%nat | 50%nat => Z_to_bv 64 (Vz j)
    | _ => getr R (reg j) end) (fun _ => [])).
  assert (vals : forall j, bv_unsigned (ev E j) = Vz j).
  { intros j. unfold E, Vz. cbn [ev].
    do 51 (destruct j as [|j]; [cbn beta iota; first [apply BG.unsigned_lit; assumption | reflexivity] |]).
    reflexivity. }
  assert (slots0 : regs_ok E PadkXJ.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. unfold PadkXJ.regs0. cbn [tl BG.slots].
    repeat apply conj; first [exact I | slotP vals]. }
  assert (know0 : know_ok RSEGS E M PadkXJ.kn0).
  { unfold know_ok, PadkXJ.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    - apply L5K.kentry_KRange with (v := V 2%nat); [evalEk vals idtac | exact sp_in].
    - apply L5K.kentry_KAlign with (v := V 2%nat); [evalEk vals idtac | lia | exact sp_al].
    - apply L5K.kentry_KWr with (a := V 2%nat) (n := 256); [evalEk vals idtac | evalEk vals idtac | lia | lia | lia | exactA sp_wr].
    - apply L5K.kentry_KRange with (v := V 50%nat); [evalEk vals idtac | exact fr_in].
    - apply L5K.kentry_KRange with (v := V 33%nat); [evalEk vals idtac | exact fi_in].
    - apply L5K.kentry_KRange with (v := V 44%nat); [evalEk vals idtac | exact sg_in].
    - apply L5K.kentry_KWord1 with (a := 0) (v := 16); [evalEk vals idtac | evalEk vals idtac | lia | lia | lia | exactA ch16]. }
  destruct (PadkXJ.seg_sound_ax fx E R M slots0 know0 ltac:(constructor))
    as (fxo & Eo & Ro & Mo & k & ps & pick & agr & run & outs & r0 & rgn & frame & cells & grow).
  apply nth_error_In in pick.
  replace PadkXJ.PSS with [PadkXJ.ps0] in pick by (vm_compute; reflexivity).
  destruct pick as [<-|[]].
  assert (same : forall a, Mo a = M a) by (intros a; apply frame; apply L5K.outside_nil_e).
  pose proof (BG.kept_regs E Eo R Ro PadkXJ.regs0 PadkXJ.regs_out0 80 KS_adkXJ KS_adkXJ_ok slots0 agr outs) as keep.
  assert (o10 : getr Ro (reg 10) = Z_to_bv 64 16).
  { rewrite (BG.out_reg PadkXJ.regs_out0 Eo Ro 10 outs) by lia. L5K.norm_expr. reflexivity. }
  assert (o11 : getr Ro (reg 11) = Z_to_bv 64 0).
  { rewrite (BG.out_reg PadkXJ.regs_out0 Eo Ro 11 outs) by lia. L5K.norm_expr. reflexivity. }
  assert (o21 : getr Ro (reg 21) = getr R (reg 21)) by (apply keep; apply L5K.in_b; vm_compute; reflexivity).
  assert (o24 : getr Ro (reg 24) = Z_to_bv 64 (V 33%nat + V 44%nat + 8)).
  { rewrite (BG.out_reg PadkXJ.regs_out0 Eo Ro 24 outs) by lia. L5K.norm_expr. wordP' vals agr. }
  exists fxo, Ro, Mo.
  refine (conj grow (conj same (conj (fun i _ => same (Z_to_bv 64 i)) (conj run (conj keep (conj o10 (conj o11 (conj o21 o24)))))))).
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkXT := LibSegBa_adkXT_b.
Definition KS_adkXT : list nat := Eval vm_compute in (BG.kept_list 80 PadkXT.regs0 PadkXT.regs_out0).
Lemma KS_adkXT_ok : BG.kept_ok 80 PadkXT.regs0 PadkXT.regs_out0 KS_adkXT = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkXT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + (V 44%nat)) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 52%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 52%nat) <= 140737488355320 -> L5KA.zeros_at M (((V 52%nat) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 52%nat) 1 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  (((V 2%nat) - 256) + 256 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 256)) -> (65536 + 6840320 <= (V 52%nat) \/ (V 52%nat) + 1 <= 65536) -> 4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 44%nat) <= 1 ->
  (((V 33%nat) + (V 44%nat)) mod 2 ^ 64) <= (V 52%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 52%nat) + 0) <= bv_unsigned a < ((V 52%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 52%nat) + 0) <= i < ((V 52%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb4a90 M) (st fx' R' 0xb46b0 M')
        /\ (forall x, In x KS_adkXT -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 0
        /\ L5.u8_at RSEGS M' (V 52%nat) 0).
Proof.
  intros w2 w33 w44 w50 w52 x2 x8 x9 x19 x20 x23 x24 x26 x27 sp_in sp_al sp_wr fr_in q_in q_sh q_wr
    q_d1 q_d2 q_d3 fi_in sg_in q_ge.
  pose (Vz := fun j : nat => match j with
    | 2%nat => V 2%nat | 33%nat => V 33%nat | 44%nat => V 44%nat | 50%nat => V 50%nat | 52%nat => V 52%nat
    | _ => bv_unsigned (getr R (reg j)) end).
  pose (E := Env (fun j : nat => match j with
    | 2%nat | 33%nat | 44%nat | 50%nat | 52%nat => Z_to_bv 64 (Vz j)
    | _ => getr R (reg j) end) (fun _ => [])).
  assert (vals : forall j, bv_unsigned (ev E j) = Vz j).
  { intros j. unfold E, Vz. cbn [ev].
    do 53 (destruct j as [|j]; [cbn beta iota; first [apply BG.unsigned_lit; assumption | reflexivity] |]).
    reflexivity. }
  assert (slots0 : regs_ok E PadkXT.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. unfold PadkXT.regs0. cbn [tl BG.slots].
    repeat apply conj; first [exact I | slotP vals]. }
  assert (know0 : know_ok RSEGS E M PadkXT.kn0).
  { unfold know_ok, PadkXT.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    - apply L5K.kentry_KRange with (v := V 2%nat); [evalEk vals idtac | exact sp_in].
    - apply L5K.kentry_KAlign with (v := V 2%nat); [evalEk vals idtac | lia | exact sp_al].
    - apply L5K.kentry_KWr with (a := V 2%nat) (n := 256); [evalEk vals idtac | evalEk vals idtac | lia | lia | lia | exactA sp_wr].
    - apply L5K.kentry_KRange with (v := V 50%nat); [evalEk vals idtac | exact fr_in].
    - apply L5K.kentry_KRange with (v := V 52%nat); [evalEk vals idtac | exact q_in].
    - apply L5KA.kentry_KZero with (a := V 52%nat / 8) (n := 1); [evalEk vals zfacts | evalEk vals idtac | zfacts; lia | lia | zfacts; lia | exact q_sh].
    - apply L5K.kentry_KWr with (a := V 52%nat) (n := 1); [evalEk vals idtac | evalEk vals idtac | lia | lia | lia | exactA q_wr].
    - apply L5K.kentry_KDisj with (a1 := 0) (n1 := 17592186048512) (a2 := V 52%nat) (n2 := 1);
        [evalEk vals idtac | evalEk vals idtac | evalEk vals idtac | evalEk vals idtac | lia].
    - apply L5K.kentry_KDisj with (a1 := V 2%nat) (n1 := 256) (a2 := V 52%nat) (n2 := 1);
        [evalEk vals idtac | evalEk vals idtac | evalEk vals idtac | evalEk vals idtac | lia].
    - apply L5K.kentry_KDisj with (a1 := 0) (n1 := 6840320) (a2 := V 52%nat) (n2 := 1);
        [evalEk vals idtac | evalEk vals idtac | evalEk vals idtac | evalEk vals idtac | lia].
    - apply L5K.kentry_KRange with (v := V 33%nat); [evalEk vals idtac | exact fi_in].
    - apply L5K.kentry_KRange with (v := V 44%nat); [evalEk vals idtac | exact sg_in].
    - apply L5K.kentry_KRange with (v := 0); [|lia].
      cbn [edenot]. rewrite u_sltu64, u_add64, !vals. unfold Vz.
      rewrite (proj2 (Z.ltb_ge _ _) q_ge). reflexivity. }
  destruct (PadkXT.seg_sound_ax fx E R M slots0 know0 ltac:(constructor))
    as (fxo & Eo & Ro & Mo & k & ps & pick & agr & run & outs & r0 & rgn & frame & cells & grow).
  apply nth_error_In in pick.
  replace PadkXT.PSS with [PadkXT.ps0] in pick by (vm_compute; reflexivity).
  destruct pick as [<-|[]].
  assert (same : forall a, ~ V 52%nat + 0 <= bv_unsigned a < V 52%nat + 0 + 1 -> Mo a = M a).
  { intros a away. apply frame.
    apply L5K.outside_cons_e with (a := V 52%nat) (n := 1); [evalEk' vals agr idtac | evalEk' vals agr idtac | exact away | apply L5K.outside_nil_e]. }
  assert (byte0 : L5.u8_at RSEGS Mo (V 52%nat) 0).
  { apply (u8_of_KWord1a Eo Mo (EVar 52) 0 (ELit 0) (V 52%nat) 0); [apply cells; vm_compute; left; reflexivity | evalEk' vals agr idtac | evalEk' vals agr idtac | lia | lia]. }
  pose proof (BG.kept_regs E Eo R Ro PadkXT.regs0 PadkXT.regs_out0 80 KS_adkXT KS_adkXT_ok slots0 agr outs) as keep.
  assert (o24 : getr Ro (reg 24) = Z_to_bv 64 (V 52%nat)).
  { rewrite (BG.out_reg PadkXT.regs_out0 Eo Ro 24 outs) by lia. L5K.norm_expr. wordP' vals agr. }
  exists fxo, Ro, Mo.
  split; [exact grow|]. split; [exact same|].
  split. { intros i iw away. apply same. rewrite BG.unsigned_lit by exact iw. exact away. }
  split; [exact run|]. split; [exact keep|].
  split. { rewrite (BG.out_reg PadkXT.regs_out0 Eo Ro 10 outs) by lia. L5K.norm_expr. reflexivity. }
  split. { rewrite (BG.out_reg PadkXT.regs_out0 Eo Ro 11 outs) by lia. L5K.norm_expr. reflexivity. }
  split; [exact o24|].
  split; [|exact byte0].
  rewrite (BG.out_reg PadkXT.regs_out0 Eo Ro 25 outs) by lia. L5K.norm_expr. reflexivity.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkXN := LibSegBa_adkXN_b.
Definition KS_adkXN : list nat := Eval vm_compute in (BG.kept_list 80 PadkXN.regs0 PadkXN.regs_out0).
Lemma KS_adkXN_ok : BG.kept_ok 80 PadkXN.regs0 PadkXN.regs_out0 KS_adkXN = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkXN_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 30) = Z_to_bv 64 ((V 33%nat) + (V 44%nat)) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 44%nat) <= 1 -> L5.u8_at RSEGS M 6759144 6 -> L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 42) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb49d8 M) (st fx' R' 0x77c94 M')
        /\ (forall x, In x KS_adkXN -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 739956
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 6759145
        /\ getr R' (reg 12) = Z_to_bv 64 3
        /\ getr R' (reg 18) = Z_to_bv 64 6759144
        /\ getr R' (reg 21) = Z_to_bv 64 (V 33%nat)).
Proof.
  intros w2 w33 w44 w50 x2 x8 x9 x18 x19 x20 x23 x26 x27 x30 sp_in sp_al sp_wr fr_in fi_in sg_in ch6 sl176.
  pose (Vz := fun j : nat => match j with
    | 2%nat => V 2%nat | 33%nat => V 33%nat | 44%nat => V 44%nat | 50%nat => V 50%nat
    | _ => bv_unsigned (getr R (reg j)) end).
  pose (E := Env (fun j : nat => match j with
    | 2%nat | 33%nat | 44%nat | 50%nat => Z_to_bv 64 (Vz j)
    | _ => getr R (reg j) end) (fun _ => [])).
  assert (vals : forall j, bv_unsigned (ev E j) = Vz j).
  { intros j. unfold E, Vz. cbn [ev].
    do 51 (destruct j as [|j]; [cbn beta iota; first [apply BG.unsigned_lit; assumption | reflexivity] |]).
    reflexivity. }
  assert (slots0 : regs_ok E PadkXN.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. unfold PadkXN.regs0. cbn [tl BG.slots].
    repeat apply conj; first [exact I | slotP vals]. }
  assert (know0 : know_ok RSEGS E M PadkXN.kn0).
  { unfold know_ok, PadkXN.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    - apply L5K.kentry_KRange with (v := V 2%nat); [evalEk vals idtac | exact sp_in].
    - apply L5K.kentry_KAlign with (v := V 2%nat); [evalEk vals idtac | lia | exact sp_al].
    - apply L5K.kentry_KWr with (a := V 2%nat) (n := 256); [evalEk vals idtac | evalEk vals idtac | lia | lia | lia | exactA sp_wr].
    - apply L5K.kentry_KRange with (v := V 50%nat); [evalEk vals idtac | exact fr_in].
    - apply L5K.kentry_KRange with (v := V 33%nat); [evalEk vals idtac | exact fi_in].
    - apply L5K.kentry_KRange with (v := V 44%nat); [evalEk vals idtac | exact sg_in].
    - apply L5K.kentry_KWord1 with (a := 0) (v := 6); [evalEk vals idtac | evalEk vals idtac | lia | lia | lia | exactA ch6].
    - apply L5K.kentry_KWord8 with (a := V 2%nat) (v := V 33%nat + 42); [evalEk vals idtac | evalEk vals idtac | lia | lia | exactA sl176]. }
  destruct (PadkXN.seg_sound_ax fx E R M slots0 know0 ltac:(constructor))
    as (fxo & Eo & Ro & Mo & k & ps & pick & agr & run & outs & r0 & rgn & frame & cells & grow).
  apply nth_error_In in pick.
  replace PadkXN.PSS with [PadkXN.ps0] in pick by (vm_compute; reflexivity).
  destruct pick as [<-|[]].
  assert (same : forall a, Mo a = M a) by (intros a; apply frame; apply L5K.outside_nil_e).
  pose proof (BG.kept_regs E Eo R Ro PadkXN.regs0 PadkXN.regs_out0 80 KS_adkXN KS_adkXN_ok slots0 agr outs) as keep.
  assert (o21 : getr Ro (reg 21) = Z_to_bv 64 (V 33%nat)).
  { rewrite (BG.out_reg PadkXN.regs_out0 Eo Ro 21 outs) by lia. L5K.norm_expr. wordP' vals agr. }
  assert (o10 : getr Ro (reg 10) = Z_to_bv 64 (V 33%nat)).
  { rewrite (BG.out_reg PadkXN.regs_out0 Eo Ro 10 outs) by lia. L5K.norm_expr. wordP' vals agr. }
  assert (o1 : getr Ro (reg 1) = Z_to_bv 64 739956).
  { rewrite (BG.out_reg PadkXN.regs_out0 Eo Ro 1 outs) by lia. L5K.norm_expr. reflexivity. }
  assert (o11 : getr Ro (reg 11) = Z_to_bv 64 6759145).
  { rewrite (BG.out_reg PadkXN.regs_out0 Eo Ro 11 outs) by lia. L5K.norm_expr. reflexivity. }
  assert (o12 : getr Ro (reg 12) = Z_to_bv 64 3).
  { rewrite (BG.out_reg PadkXN.regs_out0 Eo Ro 12 outs) by lia. L5K.norm_expr. reflexivity. }
  assert (o18 : getr Ro (reg 18) = Z_to_bv 64 6759144).
  { rewrite (BG.out_reg PadkXN.regs_out0 Eo Ro 18 outs) by lia. L5K.norm_expr. reflexivity. }
  exists fxo, Ro, Mo.
  split; [exact grow|]. split; [exact same|]. split; [intros i _; apply same|].
  split; [exact run|]. split; [exact keep|]. repeat split; assumption.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkXO := LibSegBa_adkXO_b.
Definition KS_adkXO : list nat := Eval vm_compute in (BG.kept_list 80 PadkXO.regs0 PadkXO.regs_out0).
Lemma KS_adkXO_ok : BG.kept_ok 80 PadkXO.regs0 PadkXO.regs_out0 KS_adkXO = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkXO_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 6759144 -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 44%nat) <= 1 -> L5.u8_at RSEGS M 6759144 6 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb4a74 M) (st fx' R' 0xb4ad0 M')
        /\ (forall x, In x KS_adkXO -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 6
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 33%nat) + 3)).
Proof.
  intros w2 w33 w44 w50 x2 x8 x9 x18 x19 x20 x21 x23 x26 x27 sp_in sp_al sp_wr fr_in fi_in sg_in ch6.
  pose (Vz := fun j : nat => match j with
    | 2%nat => V 2%nat | 33%nat => V 33%nat | 44%nat => V 44%nat | 50%nat => V 50%nat
    | _ => bv_unsigned (getr R (reg j)) end).
  pose (E := Env (fun j : nat => match j with
    | 2%nat | 33%nat | 44%nat | 50%nat => Z_to_bv 64 (Vz j)
    | _ => getr R (reg j) end) (fun _ => [])).
  assert (vals : forall j, bv_unsigned (ev E j) = Vz j).
  { intros j. unfold E, Vz. cbn [ev].
    do 51 (destruct j as [|j]; [cbn beta iota; first [apply BG.unsigned_lit; assumption | reflexivity] |]).
    reflexivity. }
  assert (slots0 : regs_ok E PadkXO.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. unfold PadkXO.regs0. cbn [tl BG.slots].
    repeat apply conj; first [exact I | slotP vals]. }
  assert (know0 : know_ok RSEGS E M PadkXO.kn0).
  { unfold know_ok, PadkXO.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    - apply L5K.kentry_KRange with (v := V 2%nat); [evalEk vals idtac | exact sp_in].
    - apply L5K.kentry_KAlign with (v := V 2%nat); [evalEk vals idtac | lia | exact sp_al].
    - apply L5K.kentry_KWr with (a := V 2%nat) (n := 256); [evalEk vals idtac | evalEk vals idtac | lia | lia | lia | exactA sp_wr].
    - apply L5K.kentry_KRange with (v := V 50%nat); [evalEk vals idtac | exact fr_in].
    - apply L5K.kentry_KRange with (v := V 33%nat); [evalEk vals idtac | exact fi_in].
    - apply L5K.kentry_KRange with (v := V 44%nat); [evalEk vals idtac | exact sg_in].
    - apply L5K.kentry_KWord1 with (a := 0) (v := 6); [evalEk vals idtac | evalEk vals idtac | lia | lia | lia | exactA ch6]. }
  destruct (PadkXO.seg_sound_ax fx E R M slots0 know0 ltac:(constructor))
    as (fxo & Eo & Ro & Mo & k & ps & pick & agr & run & outs & r0 & rgn & frame & cells & grow).
  apply nth_error_In in pick.
  replace PadkXO.PSS with [PadkXO.ps0] in pick by (vm_compute; reflexivity).
  destruct pick as [<-|[]].
  pose proof (BG.kept_regs E Eo R Ro PadkXO.regs0 PadkXO.regs_out0 80 KS_adkXO KS_adkXO_ok slots0 agr outs) as keep.
  assert (o24 : getr Ro (reg 24) = Z_to_bv 64 (V 33%nat + 3)).
  { rewrite (BG.out_reg PadkXO.regs_out0 Eo Ro 24 outs) by lia. L5K.norm_expr. wordP' vals agr. }
  assert (o21 : getr Ro (reg 21) = Z_to_bv 64 (V 33%nat)).
  { rewrite (BG.out_reg PadkXO.regs_out0 Eo Ro 21 outs) by lia. L5K.norm_expr. wordP' vals agr. }
  assert (o10 : getr Ro (reg 10) = Z_to_bv 64 6).
  { rewrite (BG.out_reg PadkXO.regs_out0 Eo Ro 10 outs) by lia. L5K.norm_expr. reflexivity. }
  assert (o11 : getr Ro (reg 11) = Z_to_bv 64 0).
  { rewrite (BG.out_reg PadkXO.regs_out0 Eo Ro 11 outs) by lia. L5K.norm_expr. reflexivity. }
  assert (same : forall a, Mo a = M a) by (intros a; apply frame; apply L5K.outside_nil_e).
  exists fxo, Ro, Mo. repeat split; first [assumption | intros; apply same].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkXU := LibSegBa_adkXU_b.
Definition KS_adkXU : list nat := Eval vm_compute in (BG.kept_list 80 PadkXU.regs0 PadkXU.regs_out0).
Lemma KS_adkXU_ok : BG.kept_ok 80 PadkXU.regs0 PadkXU.regs_out0 KS_adkXU = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkXU_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 21) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 52%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 52%nat) <= 140737488355320 -> L5KA.zeros_at M (((V 52%nat) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 52%nat) 1 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 1 <= 2147446784) ->
  (((V 2%nat) - 256) + 256 <= (V 52%nat) \/ (V 52%nat) + 1 <= ((V 2%nat) - 256)) -> (65536 + 6840320 <= (V 52%nat) \/ (V 52%nat) + 1 <= 65536) -> 4096 <= (V 33%nat) <= 140737488355280 -> (V 33%nat) <= (V 52%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 52%nat) + 0) <= bv_unsigned a < ((V 52%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 52%nat) + 0) <= i < ((V 52%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb4ad0 M) (st fx' R' 0xb46b0 M')
        /\ (forall x, In x KS_adkXU -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 0
        /\ L5.u8_at RSEGS M' (V 52%nat) 0).
Proof.
  intros w2 w33 w50 w52 x2 x8 x9 x19 x21 x23 x24 x26 x27 sp_in sp_al sp_wr fr_in q_in q_sh q_wr
    q_d1 q_d2 q_d3 fi_in q_ge.
  pose (Vz := fun j : nat => match j with
    | 2%nat => V 2%nat | 33%nat => V 33%nat | 50%nat => V 50%nat | 52%nat => V 52%nat
    | _ => bv_unsigned (getr R (reg j)) end).
  pose (E := Env (fun j : nat => match j with
    | 2%nat | 33%nat | 50%nat | 52%nat => Z_to_bv 64 (Vz j)
    | _ => getr R (reg j) end) (fun _ => [])).
  assert (vals : forall j, bv_unsigned (ev E j) = Vz j).
  { intros j. unfold E, Vz. cbn [ev].
    do 53 (destruct j as [|j]; [cbn beta iota; first [apply BG.unsigned_lit; assumption | reflexivity] |]).
    reflexivity. }
  assert (know0 : know_ok RSEGS E M PadkXU.kn0).
  { unfold know_ok, PadkXU.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    - apply L5K.kentry_KRange with (v := V 2%nat); [evalEk vals idtac | exact sp_in].
    - apply L5K.kentry_KAlign with (v := V 2%nat); [evalEk vals idtac | lia | exact sp_al].
    - apply L5K.kentry_KWr with (a := V 2%nat) (n := 256); [evalEk vals idtac | evalEk vals idtac | lia | lia | lia | exactA sp_wr].
    - apply L5K.kentry_KRange with (v := V 50%nat); [evalEk vals idtac | exact fr_in].
    - apply L5K.kentry_KRange with (v := V 52%nat); [evalEk vals idtac | exact q_in].
    - apply L5KA.kentry_KZero with (a := V 52%nat / 8) (n := 1); [evalEk vals zfacts | evalEk vals idtac | zfacts; lia | lia | zfacts; lia | exact q_sh].
    - apply L5K.kentry_KWr with (a := V 52%nat) (n := 1); [evalEk vals idtac | evalEk vals idtac | lia | lia | lia | exactA q_wr].
    - apply L5K.kentry_KDisj with (a1 := 0) (n1 := 17592186048512) (a2 := V 52%nat) (n2 := 1);
        [evalEk vals idtac | evalEk vals idtac | evalEk vals idtac | evalEk vals idtac | lia].
    - apply L5K.kentry_KDisj with (a1 := V 2%nat) (n1 := 256) (a2 := V 52%nat) (n2 := 1);
        [evalEk vals idtac | evalEk vals idtac | evalEk vals idtac | evalEk vals idtac | lia].
    - apply L5K.kentry_KDisj with (a1 := 0) (n1 := 6840320) (a2 := V 52%nat) (n2 := 1);
        [evalEk vals idtac | evalEk vals idtac | evalEk vals idtac | evalEk vals idtac | lia].
    - apply L5K.kentry_KRange with (v := V 33%nat); [evalEk vals idtac | exact fi_in].
    - apply L5K.kentry_KRange with (v := 0); [|lia].
      cbn [edenot]. rewrite u_sltu64, !vals. unfold Vz.
      rewrite (proj2 (Z.ltb_ge _ _) q_ge). reflexivity. }
  assert (slots0 : regs_ok E PadkXU.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. unfold PadkXU.regs0. cbn [tl BG.slots].
    repeat apply conj; first [exact I | slotP vals]. }
  destruct (PadkXU.seg_sound_ax fx E R M slots0 know0 ltac:(constructor))
    as (fxo & Eo & Ro & Mo & k & ps & pick & agr & run & outs & r0 & rgn & frame & cells & grow).
  apply nth_error_In in pick.
  replace PadkXU.PSS with [PadkXU.ps0] in pick by (vm_compute; reflexivity).
  destruct pick as [<-|[]].
  pose proof (BG.kept_regs E Eo R Ro PadkXU.regs0 PadkXU.regs_out0 80 KS_adkXU KS_adkXU_ok slots0 agr outs) as keep.
  assert (o10 : getr Ro (reg 10) = Z_to_bv 64 0).
  { rewrite (BG.out_reg PadkXU.regs_out0 Eo Ro 10 outs) by lia. L5K.norm_expr. reflexivity. }
  assert (o11 : getr Ro (reg 11) = Z_to_bv 64 0).
  { rewrite (BG.out_reg PadkXU.regs_out0 Eo Ro 11 outs) by lia. L5K.norm_expr. reflexivity. }
  assert (o25 : getr Ro (reg 25) = Z_to_bv 64 0).
  { rewrite (BG.out_reg PadkXU.regs_out0 Eo Ro 25 outs) by lia. L5K.norm_expr. reflexivity. }
  assert (o24 : getr Ro (reg 24) = Z_to_bv 64 (V 52%nat)).
  { rewrite (BG.out_reg PadkXU.regs_out0 Eo Ro 24 outs) by lia. L5K.norm_expr. wordP' vals agr. }
  assert (q52 : bv_unsigned (edenot Eo (EVar 52)) = V 52%nat) by evalEk' vals agr idtac.
  assert (byte0 : L5.u8_at RSEGS Mo (V 52%nat) 0).
  { refine (u8_of_KWord1a Eo Mo (EVar 52) 0 (ELit 0) (V 52%nat) 0 (V 52%nat) (cells _ _) q52 eq_refl ltac:(lia) ltac:(lia)).
    vm_compute. left. reflexivity. }
  assert (same : forall a, ~ V 52%nat + 0 <= bv_unsigned a < V 52%nat + 0 + 1 -> Mo a = M a).
  { intros a away. apply frame. unfold PadkXU.F0.
    refine (L5K.outside_cons_e Eo (EVar 52) 0 (ELit 1) [] a (V 52%nat) 1 q52 eq_refl away (L5K.outside_nil_e Eo a)). }
  exists fxo, Ro, Mo.
  refine (conj grow (conj same (conj _ (conj run (conj keep (conj o10 (conj o11 (conj o24 (conj o25 byte0))))))))).
  intros i iw away. apply same. rewrite BG.unsigned_lit by exact iw. exact away.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkXC := LibSegBa_adkXC_b.
Definition KS_adkXC_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkXC.regs0 PadkXC.regs_out0).
Lemma KS_adkXC_0_ok : BG.kept_ok 80 PadkXC.regs0 PadkXC.regs_out0 KS_adkXC_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkXC_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkXC.regs0 PadkXC.regs_out1).
Lemma KS_adkXC_1_ok : BG.kept_ok 80 PadkXC.regs0 PadkXC.regs_out1 KS_adkXC_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkXC_2 : list nat := Eval vm_compute in (BG.kept_list 80 PadkXC.regs0 PadkXC.regs_out2).
Lemma KS_adkXC_2_ok : BG.kept_ok 80 PadkXC.regs0 PadkXC.regs_out2 KS_adkXC_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkXC_3 : list nat := Eval vm_compute in (BG.kept_list 80 PadkXC.regs0 PadkXC.regs_out3).
Lemma KS_adkXC_3_ok : BG.kept_ok 80 PadkXC.regs0 PadkXC.regs_out3 KS_adkXC_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkXC_4 : list nat := Eval vm_compute in (BG.kept_list 80 PadkXC.regs0 PadkXC.regs_out4).
Lemma KS_adkXC_4_ok : BG.kept_ok 80 PadkXC.regs0 PadkXC.regs_out4 KS_adkXC_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkXC_5 : list nat := Eval vm_compute in (BG.kept_list 80 PadkXC.regs0 PadkXC.regs_out5).
Lemma KS_adkXC_5_ok : BG.kept_ok 80 PadkXC.regs0 PadkXC.regs_out5 KS_adkXC_5 = true. Proof. now vm_compute. Qed.
Definition KS_adkXC_6 : list nat := Eval vm_compute in (BG.kept_list 80 PadkXC.regs0 PadkXC.regs_out6).
Lemma KS_adkXC_6_ok : BG.kept_ok 80 PadkXC.regs0 PadkXC.regs_out6 KS_adkXC_6 = true. Proof. now vm_compute. Qed.
Lemma adkXC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 11) = Z_to_bv 64 (V 36%nat) -> getr R (reg 13) = Z_to_bv 64 (V 39%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 30) = Z_to_bv 64 ((V 33%nat) + (V 44%nat)) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= (V 44%nat) <= 1 -> L5.img_clear M 65536 1282048 -> 0 <= (V 39%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 64) -> ~ (((V 2%nat) - 168) <= bv_unsigned a < ((V 2%nat) - 168) + 8) -> ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 64) -> ~ (((V 2%nat) - 168) <= i < ((V 2%nat) - 168) + 8) -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb4a04 M) (st fx' R' 0xb425c M')
        /\ (forall x, In x KS_adkXC_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551608
        /\ bv_unsigned (getr R' (reg 12)) = (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 35%nat) / 4294967296)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 39%nat) / 32768)
        /\ ((((V 35%nat) / 4294967296) - 0) mod 2 ^ 64) < 1
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) ((V 35%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (V 36%nat))
      \/ (msteps RSEGS (st fx R 0xb4a04 M) (st fx' R' 0xb425c M')
        /\ (forall x, In x KS_adkXC_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
        /\ getr R' (reg 10) = Z_to_bv 64 7
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551608
        /\ bv_unsigned (getr R' (reg 12)) = (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 35%nat) / 4294967296)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 39%nat) / 32768)
        /\ 7 < (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64)
        /\ ((((V 35%nat) / 4294967296) - 0) mod 2 ^ 64) < 1
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) ((V 35%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (V 36%nat))
      \/ (msteps RSEGS (st fx R 0xb4a04 M) (st fx' R' 0xb4164 M')
        /\ (forall x, In x KS_adkXC_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
        /\ getr R' (reg 10) = Z_to_bv 64 3
        /\ getr R' (reg 11) = Z_to_bv 64 18446744072850558976
        /\ getr R' (reg 12) = Z_to_bv 64 1000001536
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 35%nat) / 4294967296)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 39%nat) / 32768)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 1000000000
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 23) = Z_to_bv 64 14757395259826634752
        /\ getr R' (reg 25) = Z_to_bv 64 19342813113834067
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 50%nat) + 172)
        /\ getr R' (reg 27) = Z_to_bv 64 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 50%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (((V 50%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 33%nat) + (V 44%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) ((V 39%nat) / 32768)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 16383
        /\ (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64) <= 7
        /\ ((((V 35%nat) / 4294967296) - 0) mod 2 ^ 64) < 1
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) ((V 35%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (V 36%nat))
      \/ (msteps RSEGS (st fx R 0xb4a04 M) (st fx' R' 0xb425c M')
        /\ (forall x, In x KS_adkXC_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
        /\ getr R' (reg 10) = Z_to_bv 64 7
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551608
        /\ bv_unsigned (getr R' (reg 12)) = (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 35%nat) / 4294967296)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 39%nat) / 32768)
        /\ 7 < (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64)
        /\ 1 <= ((((V 35%nat) / 4294967296) - 0) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) ((V 35%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (V 36%nat))
      \/ (msteps RSEGS (st fx R 0xb4a04 M) (st fx' R' 0xb4164 M')
        /\ (forall x, In x KS_adkXC_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
        /\ getr R' (reg 10) = Z_to_bv 64 3
        /\ getr R' (reg 11) = Z_to_bv 64 18446744072850558976
        /\ getr R' (reg 12) = Z_to_bv 64 1000001536
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 35%nat) / 4294967296)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 39%nat) / 32768)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 1000000000
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 23) = Z_to_bv 64 14757395259826634752
        /\ getr R' (reg 25) = Z_to_bv 64 19342813113834067
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 50%nat) + 172)
        /\ getr R' (reg 27) = Z_to_bv 64 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 50%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (((V 50%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 33%nat) + (V 44%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) ((V 39%nat) / 32768)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 16383
        /\ (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64) <= 7
        /\ 1 <= ((((V 35%nat) / 4294967296) - 0) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) ((V 35%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (V 36%nat))
      \/ (msteps RSEGS (st fx R 0xb4a04 M) (st fx' R' 0xb425c M')
        /\ (forall x, In x KS_adkXC_5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
        /\ getr R' (reg 10) = Z_to_bv 64 7
        /\ bv_unsigned (getr R' (reg 12)) = (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 35%nat) / 4294967296)
        /\ bv_unsigned (getr R' (reg 14)) = ((((((16384 * (((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64) + 131072) mod 2 ^ 64)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 39%nat) / 32768)
        /\ 7 < (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) ((V 35%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (V 36%nat))
      \/ (msteps RSEGS (st fx R 0xb4a04 M) (st fx' R' 0xb4164 M')
        /\ (forall x, In x KS_adkXC_6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
        /\ getr R' (reg 10) = Z_to_bv 64 3
        /\ getr R' (reg 11) = Z_to_bv 64 18446744072850558976
        /\ getr R' (reg 12) = Z_to_bv 64 1000001536
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 35%nat) / 4294967296)
        /\ bv_unsigned (getr R' (reg 14)) = ((((((16384 * (((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64) + 131072) mod 2 ^ 64)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 39%nat) / 32768)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 1000000000
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 23) = Z_to_bv 64 14757395259826634752
        /\ getr R' (reg 25) = Z_to_bv 64 19342813113834067
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 50%nat) + 172)
        /\ getr R' (reg 27) = Z_to_bv 64 10
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 50%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (((V 50%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 33%nat) + (V 44%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) ((V 39%nat) / 32768)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 16383
        /\ (((((131072 * (V 36%nat)) mod 2 ^ 64) / 9223372036854775808) + 8) mod 2 ^ 64) <= 7
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) ((V 35%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (V 36%nat))).
Proof.
  intros w2 w33 w35 w36 w39 w44 w50 x2 x8 x9 x10 x11 x13 x18 x19 x20 x23 x26 x27 x30
    sp_in sp_al sp_wr fr_in fi_in sg_in img hi_in.
  pose (Vz := fun j : nat => match j with
    | 2%nat => V 2%nat | 33%nat => V 33%nat | 35%nat => V 35%nat | 36%nat => V 36%nat
    | 39%nat => V 39%nat | 44%nat => V 44%nat | 50%nat => V 50%nat
    | _ => bv_unsigned (getr R (reg j)) end).
  pose (E := Env (fun j : nat => match j with
    | 2%nat | 33%nat | 35%nat | 36%nat | 39%nat | 44%nat | 50%nat => Z_to_bv 64 (Vz j)
    | _ => getr R (reg j) end) (fun _ => [])).
  assert (vals : forall j, bv_unsigned (ev E j) = Vz j).
  { intros j. unfold E, Vz. cbn [ev].
    do 51 (destruct j as [|j]; [cbn beta iota; first [apply BG.unsigned_lit; assumption | reflexivity] |]).
    reflexivity. }
  assert (slots0 : regs_ok E PadkXC.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. unfold PadkXC.regs0. cbn [tl BG.slots].
    repeat apply conj; first [exact I | slotP vals]. }
  assert (know0 : know_ok RSEGS E M PadkXC.kn0).
  { unfold know_ok, PadkXC.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    - apply L5K.kentry_KRange with (v := V 2%nat); [evalEk vals idtac | exact sp_in].
    - apply L5K.kentry_KAlign with (v := V 2%nat); [evalEk vals idtac | lia | exact sp_al].
    - apply L5K.kentry_KWr with (a := V 2%nat) (n := 256); [evalEk vals idtac | evalEk vals idtac | lia | lia | lia | exactA sp_wr].
    - apply L5K.kentry_KRange with (v := V 50%nat); [evalEk vals idtac | exact fr_in].
    - apply L5K.kentry_KRange with (v := V 33%nat); [evalEk vals idtac | exact fi_in].
    - apply L5K.kentry_KRange with (v := V 44%nat); [evalEk vals idtac | exact sg_in].
    - apply L5K.kentry_KImg; [lia | lia | exact img].
    - apply L5K.kentry_KRange with (v := V 39%nat); [evalEk vals idtac | exact hi_in]. }
  destruct (PadkXC.seg_sound_ax fx E R M slots0 know0 ltac:(constructor))
    as (fxo & Eo & Ro & Mo & k & ps & pick & agr & run & outs & r0 & rgn & frame & cells & grow).
  assert (h2o : bv_unsigned (edenot Eo (EVar 2)) = V 2%nat) by evalEk' vals agr idtac.
  assert (h35 : bv_unsigned (ev Eo 35) = V 35%nat).
  { rewrite <- (proj1 agr 35%nat) by (unfold PadkXC.NX0; lia). exact (vals 35%nat). }
  assert (h36 : bv_unsigned (ev Eo 36) = V 36%nat).
  { rewrite <- (proj1 agr 36%nat) by (unfold PadkXC.NX0; lia). exact (vals 36%nat). }
  assert (h39 : bv_unsigned (ev Eo 39) = V 39%nat).
  { rewrite <- (proj1 agr 39%nat) by (unfold PadkXC.NX0; lia). exact (vals 39%nat). }
  pose (e12 := EAlu ALU_ADD (EAlu ALU_SRL (EMd M_MUL (ELit 131072) (EVar 36)) (ELit 63)) (ELit 8)).
  assert (t12 : bv_unsigned (edenot Eo e12) = ((131072 * V 36%nat) mod 2 ^ 64 / 9223372036854775808 + 8) mod 2 ^ 64).
  { unfold e12. cbn [edenot]. rewrite u_add64, u_srl64, u_mul64, h36, !BG.unsigned_lit by lia. reflexivity. }
  assert (t14 : bv_unsigned (edenot Eo (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 16384)
      (EAlu ALU_SRL (EMd M_MUL (ELit 131072) (EVar 36)) (ELit 63))) (EAlu ALU_AND (EVar 39) (ELit 16383))) (ELit 131072)))
      = (((16384 * ((131072 * V 36%nat) mod 2 ^ 64 / 9223372036854775808)) mod 2 ^ 64 + Z.land (V 39%nat) 16383) mod 2 ^ 64
         + 131072) mod 2 ^ 64).
  { cbn [edenot]. rewrite u_add64, u_add64, u_mul64, u_srl64, u_mul64, u_and64, h36, h39, !BG.unsigned_lit by lia.
    reflexivity. }
  assert (s35 : bv_unsigned (edenot Eo (EAlu ALU_SUB (EAlu ALU_SRL (EVar 35) (ELit 32)) (ELit 0)))
      = (V 35%nat / 4294967296 - 0) mod 2 ^ 64).
  { cbn [edenot]. rewrite u_sub64, u_srl64, h35, !BG.unsigned_lit by lia. reflexivity. }
  assert (ltu : forall a b lo hi, kentry_ok RSEGS Eo Mo (KRange (EAlu ALU_SLTU a b) lo hi) ->
      lo <= (if bv_unsigned (edenot Eo a) <? bv_unsigned (edenot Eo b) then 1 else 0) <= hi).
  { intros a b lo hi cell. exact (L5K.range_of_KRange _ _ _ _ _ _ _ cell (u_sltu64 _ _)). }
  assert (on35 : kentry_ok RSEGS Eo Mo (KRange (EAlu ALU_SLTU (EAlu ALU_SUB (EAlu ALU_SRL (EVar 35) (ELit 32)) (ELit 0)) (ELit 1)) 1 1)
      -> (V 35%nat / 4294967296 - 0) mod 2 ^ 64 < 1).
  { intros cell. apply ltu in cell. rewrite s35 in cell. change (bv_unsigned (edenot Eo (ELit 1))) with 1 in cell.
    destruct ((V 35%nat / 4294967296 - 0) mod 2 ^ 64 <? 1) eqn:b; [apply Z.ltb_lt; exact b | lia]. }
  assert (off35 : kentry_ok RSEGS Eo Mo (KRange (EAlu ALU_SLTU (EAlu ALU_SUB (EAlu ALU_SRL (EVar 35) (ELit 32)) (ELit 0)) (ELit 1)) 0 0)
      -> 1 <= (V 35%nat / 4294967296 - 0) mod 2 ^ 64).
  { intros cell. apply ltu in cell. rewrite s35 in cell. change (bv_unsigned (edenot Eo (ELit 1))) with 1 in cell.
    destruct ((V 35%nat / 4294967296 - 0) mod 2 ^ 64 <? 1) eqn:b; [lia | apply Z.ltb_ge; exact b]. }
  assert (on7 : kentry_ok RSEGS Eo Mo (KRange (EAlu ALU_SLTU (ELit 7) e12) 1 1)
      -> 7 < ((131072 * V 36%nat) mod 2 ^ 64 / 9223372036854775808 + 8) mod 2 ^ 64).
  { intros cell. apply ltu in cell. rewrite t12 in cell. change (bv_unsigned (edenot Eo (ELit 7))) with 7 in cell.
    destruct (7 <? ((131072 * V 36%nat) mod 2 ^ 64 / 9223372036854775808 + 8) mod 2 ^ 64) eqn:b; [apply Z.ltb_lt; exact b | lia]. }
  assert (off7 : kentry_ok RSEGS Eo Mo (KRange (EAlu ALU_SLTU (ELit 7) e12) 0 0)
      -> ((131072 * V 36%nat) mod 2 ^ 64 / 9223372036854775808 + 8) mod 2 ^ 64 <= 7).
  { intros cell. apply ltu in cell. rewrite t12 in cell. change (bv_unsigned (edenot Eo (ELit 7))) with 7 in cell.
    destruct (7 <? ((131072 * V 36%nat) mod 2 ^ 64 / 9223372036854775808 + 8) mod 2 ^ 64) eqn:b; [lia | apply Z.ltb_ge; exact b]. }
  assert (same : forall a, ~ V 2%nat - 240 <= bv_unsigned a < V 2%nat - 240 + 64 -> ~ V 2%nat - 168 <= bv_unsigned a < V 2%nat - 168 + 8 ->
      ~ V 2%nat - 136 <= bv_unsigned a < V 2%nat - 136 + 16 -> Mo a = M a).
  { intros a n240 n168 n136. apply frame. unfold PadkXC.F0.
    apply (L5K.outside_cons_e Eo (EVar 2) (-240) (ELit 64) _ a (V 2%nat) 64 h2o eq_refl); [intros [lo hi]; apply n240; split; lia|].
    apply (L5K.outside_cons_e Eo (EVar 2) (-168) (ELit 8) _ a (V 2%nat) 8 h2o eq_refl); [intros [lo hi]; apply n168; split; lia|].
    apply (L5K.outside_cons_e Eo (EVar 2) (-136) (ELit 16) _ a (V 2%nat) 16 h2o eq_refl); [intros [lo hi]; apply n136; split; lia|].
    apply L5K.outside_nil_e. }
  exists fxo, Ro, Mo.
  split; [exact grow|]. split; [exact same|].
  split. { intros i iw n240 n168 n136. apply same; rewrite BG.unsigned_lit by exact iw; assumption. }
  apply nth_error_In in pick.
  replace PadkXC.PSS with [PadkXC.ps0; PadkXC.ps1; PadkXC.ps2; PadkXC.ps3; PadkXC.ps4; PadkXC.ps5; PadkXC.ps6] in pick
    by (vm_compute; reflexivity).
  destruct pick as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];
    [ left; split; [exact run|]; split;
        [exact (BG.kept_regs E Eo R Ro PadkXC.regs0 PadkXC.regs_out0 80 KS_adkXC_0 KS_adkXC_0_ok slots0 agr outs)|]
    | right; left; split; [exact run|]; split;
        [exact (BG.kept_regs E Eo R Ro PadkXC.regs0 PadkXC.regs_out1 80 KS_adkXC_1 KS_adkXC_1_ok slots0 agr outs)|]
    | do 2 right; left; split; [exact run|]; split;
        [exact (BG.kept_regs E Eo R Ro PadkXC.regs0 PadkXC.regs_out2 80 KS_adkXC_2 KS_adkXC_2_ok slots0 agr outs)|]
    | do 3 right; left; split; [exact run|]; split;
        [exact (BG.kept_regs E Eo R Ro PadkXC.regs0 PadkXC.regs_out3 80 KS_adkXC_3 KS_adkXC_3_ok slots0 agr outs)|]
    | do 4 right; left; split; [exact run|]; split;
        [exact (BG.kept_regs E Eo R Ro PadkXC.regs0 PadkXC.regs_out4 80 KS_adkXC_4 KS_adkXC_4_ok slots0 agr outs)|]
    | do 5 right; left; split; [exact run|]; split;
        [exact (BG.kept_regs E Eo R Ro PadkXC.regs0 PadkXC.regs_out5 80 KS_adkXC_5 KS_adkXC_5_ok slots0 agr outs)|]
    | do 6 right; split; [exact run|]; split;
        [exact (BG.kept_regs E Eo R Ro PadkXC.regs0 PadkXC.regs_out6 80 KS_adkXC_6 KS_adkXC_6_ok slots0 agr outs)|] ].
  all: pose proof (proj2 (Forall_forall _ _) cells) as held;
    cbv [SR.ps_cells PadkXC.ps0 PadkXC.ps1 PadkXC.ps2 PadkXC.ps3 PadkXC.ps4 PadkXC.ps5 PadkXC.ps6
         PadkXC.cells0 PadkXC.cells1 PadkXC.cells2 PadkXC.cells3 PadkXC.cells4 PadkXC.cells5 PadkXC.cells6] in held;
    repeat (let c := fresh "cell" in apply Forall_cons_iff in held; destruct held as [c held]).
  all: repeat match goal with |- _ /\ _ => split end.
  all: lazymatch goal with
    | |- getr _ (Z_to_bv 5 (Z.of_nat ?r)) = _ =>
        rewrite (BG.out_reg _ Eo Ro r outs) by (clear; lia); L5K.norm_expr; lazymatch goal with |- edenot _ (ELit _) = _ => reflexivity | _ => wordP' vals agr end
    | |- bv_unsigned (getr _ (Z_to_bv 5 (Z.of_nat ?r))) = _ =>
        rewrite (BG.out_reg _ Eo Ro r outs) by (clear; lia); L5K.norm_expr; first [exact t12 | exact t14]
    | |- L5.u64_at _ _ _ _ =>
        match goal with c : kentry_ok _ _ _ (KWord _ 8 _) |- _ =>
          eapply (u64_of_KWord8a _ _ _ _ _ _ _ _ c); [exact h2o | | reflexivity]; evalEk' vals agr zfacts end
    | |- L5.u32_at _ _ _ _ =>
        match goal with c : kentry_ok _ _ _ (KWord _ 4 _) |- _ =>
          eapply (u32_of_KWord4a _ _ _ _ _ _ _ _ c); [exact h2o | | reflexivity]; evalEk' vals agr zfacts end
    | |- _ => first [apply on35 | apply off35 | apply on7 | apply off7]; assumption
    end.
Qed.
(* [comment removed for export] *)

End PNADP7.
