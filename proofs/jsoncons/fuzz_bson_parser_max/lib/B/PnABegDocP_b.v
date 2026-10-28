(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BigLinkZA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0PlanKit_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_abdA_b LibSegBa_abdB_b LibSegBa_abdBx_b LibSegBa_abdR_b LibSegBa_abdV_b LibSegBa_abdT_b LibSegBa_abdE4_b LibSegBa_abdE1_b LibSegBa_abdU_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNABDP.
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
Module PabdA := LibSegBa_abdA_b.
Definition KS_abdA : list nat := Eval vm_compute in (BG.kept_list 80 PabdA.regs0 PabdA.regs_out0).
Lemma KS_abdA_ok : BG.kept_ok 80 PabdA.regs0 PabdA.regs_out0 KS_abdA = true. Proof. vm_compute. reflexivity. Qed.
Lemma abdA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 36%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae924 M) (st fx' R' 0x5dc2c M')
        /\ (forall x, In x KS_abdA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 715164
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G10 G11 G12 K0 K1 K2 pvzI5 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PabdA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabdA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabdA.kn0).
  { unfold know_ok, PabdA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabdA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabdA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 160) <= bv_unsigned a < (vz_2 - 160) + 160) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PabdA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabdA.ps0) with 0x5dc2c in Hms. change (SR.ps_regs PabdA.ps0) with (map (fun i => (i, nth i PabdA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabdA.ps0) with PabdA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabdA.regs0 PabdA.regs_out0 80 KS_abdA KS_abdA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabdA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PabdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PabdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PabdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PabdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PabdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdA.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PabdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdA.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PabdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabdB := LibSegBa_abdB_b.
Definition KS_abdB : list nat := Eval vm_compute in (BG.kept_list 80 PabdB.regs0 PabdB.regs_out0).
Lemma KS_abdB_ok : BG.kept_ok 80 PabdB.regs0 PabdB.regs_out0 KS_abdB = true. Proof. vm_compute. reflexivity. Qed.
Lemma abdB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 (V 34%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 312) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + (V 42%nat)) ->
  4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 8 -> 40 <= (V 42%nat) <= 41000 -> aligned (V 42%nat) 8 ->
  L5.u32_at RSEGS M ((V 33%nat) + 312) 1024 -> 1 <= bv_unsigned (sext 64 (mul_div Instr.M_MUL (low32 (alu64 Instr.ALU_SRA (Z_to_bv 64 (V 42%nat)) (Z_to_bv 64 3))) (low32 (Z_to_bv 64 14757395258967641293)))) <= 1024 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 8) -> ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 8) -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae99c M) (st fx' R' 0xaed4c M')
        /\ (forall x, In x KS_abdB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 715444
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 4
        /\ getr R' (reg 13) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 18) = Z_to_bv 64 4
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 2147450880
        /\ getr R' (reg 20) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 4
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 33%nat) + 400)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((V 33%nat) + 392)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 243
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) 715044
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) 96701
        /\ L5.u64_at RSEGS M' (V 50%nat) 1102416563
        /\ L5.defined M' ((V 50%nat) + 24) 40).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G19 G20 G23 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 pvzI12 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 pvzI13 K33 pvzI14 K35 K36 pvzI15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K32l; move K32l before pvzI13; pose proof (proj2 pvzI13) as K32r; move K32r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K34l; move K34l before pvzI14; pose proof (proj2 pvzI14) as K34r; move K34r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K37l; move K37l before pvzI15; pose proof (proj2 pvzI15) as K37r; move K37r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 41%nat => vz_41 | 42%nat => vz_42 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PabdB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabdB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabdB.kn0).
  { unfold know_ok, PabdB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear - HV41l HV41r K32l K32r) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear - HV41l HV41r K32l K32r HV42l HV42r K34l K34r) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K32l K32r) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K34l K34r) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K34l K34r) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [cbn [edenot ev]; reflexivity | exact (conj K37l K37r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabdB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabdB.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 24) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 8) -> ~ ((vz_2 - 144) <= bv_unsigned a < (vz_2 - 144) + 16) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PabdB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabdB.ps0) with 0xaed4c in Hms. change (SR.ps_regs PabdB.ps0) with (map (fun i => (i, nth i PabdB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabdB.ps0) with PabdB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabdB.regs0 PabdB.regs_out0 80 KS_abdB KS_abdB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabdB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PabdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PabdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PabdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdB.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PabdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdB.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PabdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdB.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PabdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdB.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PabdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdB.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PabdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdB.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PabdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdB.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PabdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdB.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PabdB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabdBx := LibSegBa_abdBx_b.
Definition KS_abdBx : list nat := Eval vm_compute in (BG.kept_list 80 PabdBx.regs0 PabdBx.regs_out0).
Lemma KS_abdBx_ok : BG.kept_ok 80 PabdBx.regs0 PabdBx.regs_out0 KS_abdBx = true. Proof. vm_compute. reflexivity. Qed.
Lemma abdBx_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 (V 34%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 312) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + (V 42%nat)) ->
  4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 8 -> 40 <= (V 42%nat) <= 41000 -> aligned (V 42%nat) 8 ->
  L5.u32_at RSEGS M ((V 33%nat) + 312) 1024 -> 1025 <= bv_unsigned (sext 64 (mul_div Instr.M_MUL (low32 (alu64 Instr.ALU_SRA (Z_to_bv 64 (V 42%nat)) (Z_to_bv 64 3))) (low32 (Z_to_bv 64 14757395258967641293)))) <= 1025 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xae99c M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_abdBx -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 715920
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 4
        /\ getr R' (reg 13) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 18) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (((V 33%nat) + 400) / 8)
        /\ getr R' (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) (V 50%nat)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 248
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) 715044
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) 96701
        /\ L5.u64_at RSEGS M' (V 50%nat) 1102416563
        /\ L5.defined M' ((V 50%nat) + 24) 40).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G19 G20 G23 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 K12 K13 pvzI11 K15 K16 K17 K18 K19 K20 pvzI12 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 pvzI13 K33 pvzI14 K35 K36 pvzI15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K14l; move K14l before pvzI11; pose proof (proj2 pvzI11) as K14r; move K14r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K21l; move K21l before pvzI12; pose proof (proj2 pvzI12) as K21r; move K21r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K32l; move K32l before pvzI13; pose proof (proj2 pvzI13) as K32r; move K32r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K34l; move K34l before pvzI14; pose proof (proj2 pvzI14) as K34r; move K34r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K37l; move K37l before pvzI15; pose proof (proj2 pvzI15) as K37r; move K37r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 41%nat => vz_41 | 42%nat => vz_42 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PabdBx.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabdBx.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabdBx.kn0).
  { unfold know_ok, PabdBx.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear - HV41l HV41r K32l K32r) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear - HV41l HV41r K32l K32r HV42l HV42r K34l K34r) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K32l K32r) | clear; lia | exact K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K34l K34r) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K34l K34r) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [cbn [edenot ev]; reflexivity | exact (conj K37l K37r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabdBx.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabdBx.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 24) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PabdBx.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabdBx.ps0) with 0xae848 in Hms. change (SR.ps_regs PabdBx.ps0) with (map (fun i => (i, nth i PabdBx.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabdBx.ps0) with PabdBx.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabdBx.regs0 PabdBx.regs_out0 80 KS_abdBx KS_abdBx_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabdBx.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabdBx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdBx.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabdBx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdBx.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabdBx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdBx.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PabdBx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdBx.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PabdBx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdBx.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PabdBx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdBx.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PabdBx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdBx.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PabdBx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdBx.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PabdBx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdBx.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PabdBx.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabdR := LibSegBa_abdR_b.
Definition KS_abdR_0 : list nat := Eval vm_compute in (BG.kept_list 80 PabdR.regs0 PabdR.regs_out0).
Lemma KS_abdR_0_ok : BG.kept_ok 80 PabdR.regs0 PabdR.regs_out0 KS_abdR_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_abdR_1 : list nat := Eval vm_compute in (BG.kept_list 80 PabdR.regs0 PabdR.regs_out1).
Lemma KS_abdR_1_ok : BG.kept_ok 80 PabdR.regs0 PabdR.regs_out1 KS_abdR_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma abdR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 45%nat) -> getr R (reg 18) = Z_to_bv 64 4 -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 50%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 34%nat) -> getr R (reg 24) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 25) = Z_to_bv 64 (V 50%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 312) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> 0 <= (V 45%nat) <= 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xaeab4 M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_abdR_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 715960
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ 1 <= (((V 45%nat) - 4) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 45%nat))
      \/ (msteps RSEGS (st fx R 0xaeab4 M) (st fx' R' 0xaeabc M')
        /\ (forall x, In x KS_abdR_1 -> getr R' (reg x) = getr R (reg x))
        /\ (((V 45%nat) - 4) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 45%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 K20 pvzI11 K22 K23 K24 K25 K26 K27 K28 K29 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV45l; move HV45l before pvzI5; pose proof (proj2 pvzI5) as HV45r; move HV45r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K21l; move K21l before pvzI11; pose proof (proj2 pvzI11) as K21r; move K21r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K30l; move K30l before pvzI12; pose proof (proj2 pvzI12) as K30r; move K30r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 45%nat => Z_to_bv 64 vz_45 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 45%nat => vz_45 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PabdR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabdR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabdR.kn0).
  { unfold know_ok, PabdR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K30l K30r) | exact (conj K30l K30r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabdR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabdR.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PabdR.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PabdR.ps0) with 0xae848 in Hms. change (SR.ps_regs PabdR.ps0) with (map (fun i => (i, nth i PabdR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PabdR.ps0) with PabdR.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PabdR.regs0 PabdR.regs_out0 80 KS_abdR_0 KS_abdR_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PabdR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabdR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabdR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdR.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabdR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk' ZA Hag ltac:(clear - HV45l HV45r K30l K30r) | clear; lia]. 
  - right.
    change (SR.ps_pc PabdR.ps1) with 0xaeabc in Hms. change (SR.ps_regs PabdR.ps1) with (map (fun i => (i, nth i PabdR.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PabdR.ps1) with PabdR.cells1 in Hcells. unfold PabdR.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PabdR.regs0 PabdR.regs_out1 80 KS_abdR_1 KS_abdR_1_ok HR Hag Hregs j Hj). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk' ZA Hag ltac:(clear - HV45l HV45r K30l K30r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabdV := LibSegBa_abdV_b.
Definition KS_abdV_0 : list nat := Eval vm_compute in (BG.kept_list 80 PabdV.regs0 PabdV.regs_out0).
Lemma KS_abdV_0_ok : BG.kept_ok 80 PabdV.regs0 PabdV.regs_out0 KS_abdV_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_abdV_1 : list nat := Eval vm_compute in (BG.kept_list 80 PabdV.regs0 PabdV.regs_out1).
Lemma KS_abdV_1_ok : BG.kept_ok 80 PabdV.regs0 PabdV.regs_out1 KS_abdV_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma abdV_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 4 -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 50%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 34%nat) -> getr R (reg 24) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 25) = Z_to_bv 64 (V 50%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 312) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 224) + 224 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 224)) -> (((V 2%nat) - 224) + 224 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 224)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> 6905856 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 224) + 224 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 224)) -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  ((V 50%nat) + 64 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 50%nat)) -> ((V 51%nat) + 1 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 51%nat)) -> L5.u64_at RSEGS M (V 34%nat) 1251456 -> L5KA.zeros_at M 2147607320 1 ->
  ((((V 34%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 34%nat) / 8) + 2147450880)) -> L5.u32_at RSEGS M ((V 50%nat) + 32) (V 46%nat) -> 0 <= (V 46%nat) <= 4294967295 -> L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  L5.u8_at RSEGS M ((V 33%nat) + 10) 0 ->
  0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + (V 42%nat)) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 41%nat) + (V 43%nat)) ->
  4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 8 -> 40 <= (V 42%nat) <= 41000 -> aligned (V 42%nat) 8 -> 40 <= (V 43%nat) <= 81920 -> aligned (V 43%nat) 8 ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 33%nat) + 392) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 33%nat) + 400) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> ~ (((V 2%nat) - 224) <= bv_unsigned a < ((V 2%nat) - 224) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 8) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> ~ (((V 2%nat) - 224) <= i < ((V 2%nat) - 224) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xaeabc M) (st fx' R' 0xb2758 M')
        /\ (forall x, In x KS_abdV_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 715700
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 116)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 50%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 120) 2
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 1
        /\ ((V 41%nat) + (V 43%nat)) mod 2 ^ 64 <= ((V 41%nat) + (V 42%nat)) mod 2 ^ 64)
      \/ (msteps RSEGS (st fx R 0xaeabc M) (st fx' R' 0xad4b8 M')
        /\ (forall x, In x KS_abdV_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 730612
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 224)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 116)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 18446744073709551576
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ ((V 41%nat) + (V 42%nat)) mod 2 ^ 64 < ((V 41%nat) + (V 43%nat)) mod 2 ^ 64
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) ((V 41%nat) + (V 42%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) ((V 41%nat) + (V 42%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) ((V 41%nat) + (V 42%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) ((V 2%nat) - 160)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (V 2%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 715660
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 120) 2
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 K12 K13 pvzI10 K15 K16 K17 K18 K19 K20 pvzI11 K22 K23 K24 K25 K26 K27 K28 K29 pvzI12 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI13 K43 K44 HB41 HB42 HB43 KV1 KV2 KV3 KR41 KA41 KR42 KA42 KR43 KA43 KS136 KS144.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV46l; move HV46l before pvzI5; pose proof (proj2 pvzI5) as HV46r; move HV46r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K21l; move K21l before pvzI11; pose proof (proj2 pvzI11) as K21r; move K21r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K30l; move K30l before pvzI12; pose proof (proj2 pvzI12) as K30r; move K30r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K42l; move K42l before pvzI13; pose proof (proj2 pvzI13) as K42r; move K42r before pvzI13; clear pvzI13. destruct HB41 as [HV41l HV41r]. destruct HB42 as [HV42l HV42r]. destruct HB43 as [HV43l HV43r]. destruct KR41 as [KR41l KR41r]. destruct KR42 as [KR42l KR42r]. destruct KR43 as [KR43l KR43r].
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 46%nat => Z_to_bv 64 vz_46 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 46%nat => vz_46 | 50%nat => vz_50 | 51%nat => vz_51 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PabdV.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabdV.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabdV.kn0).
  { unfold know_ok, PabdV.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40) | exact (conj K30l K30r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40; lia | clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40; lia | clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40; lia | clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40; lia | exactA K38]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40) | evalEk ZA ltac:(clear - HV46l HV46r K42l K42r) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | byte_tac ltac:(clear) | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk ZA ltac:(clear - HV41l HV41r KR41l KR41r) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | exactA KV1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk ZA ltac:(clear - HV41l HV41r KR41l KR41r HV42l HV42r KR42l KR42r) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | exactA KV2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk ZA ltac:(clear - HV41l HV41r KR41l KR41r HV43l HV43r KR43l KR43r) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35; lia | exactA KV3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r KR41l KR41r) | exact (conj KR41l KR41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r KR41l KR41r) | clear; lia | exact KA41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r KR42l KR42r) | exact (conj KR42l KR42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r KR42l KR42r) | clear; lia | exact KA42]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r KR43l KR43r) | exact (conj KR43l KR43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV43l HV43r KR43l KR43r) | clear; lia | exact KA43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34; lia | exactA KS136]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34; lia | exactA KS144]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabdV.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabdV.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 8) -> ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> ~ ((vz_2 - 224) <= bv_unsigned a < (vz_2 - 224) + 64) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PabdV.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PabdV.ps0) with 0xb2758 in Hms. change (SR.ps_regs PabdV.ps0) with (map (fun i => (i, nth i PabdV.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PabdV.ps0) with PabdV.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PabdV.regs0 PabdV.regs_out0 80 KS_abdV_0 KS_abdV_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PabdV.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabdV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdV.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabdV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdV.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabdV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdV.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabdV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdV.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PabdV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdV.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PabdV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdV.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PabdV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  - right.
    change (SR.ps_pc PabdV.ps1) with 0xad4b8 in Hms. change (SR.ps_regs PabdV.ps1) with (map (fun i => (i, nth i PabdV.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PabdV.ps1) with PabdV.cells1 in Hcells. unfold PabdV.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PabdV.regs0 PabdV.regs_out1 80 KS_abdV_1 KS_abdV_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PabdV.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PabdV.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdV.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PabdV.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdV.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PabdV.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdV.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PabdV.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdV.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PabdV.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdV.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PabdV.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdV.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PabdV.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdV.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PabdV.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdV.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PabdV.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PabdV.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PabdV.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk' ZA Hag ltac:(clear - HV41l HV41r KR41l KR41r HV42l HV42r KR42l KR42r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk' ZA Hag ltac:(clear - HV41l HV41r KR41l KR41r HV42l HV42r KR42l KR42r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk' ZA Hag ltac:(clear - HV41l HV41r KR41l KR41r HV42l HV42r KR42l KR42r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabdT := LibSegBa_abdT_b.
Definition KS_abdT : list nat := Eval vm_compute in (BG.kept_list 80 PabdT.regs0 PabdT.regs_out0).
Lemma KS_abdT_ok : BG.kept_ok 80 PabdT.regs0 PabdT.regs_out0 KS_abdT = true. Proof. vm_compute. reflexivity. Qed.
Lemma abdT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 20) = Z_to_bv 64 (V 50%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 34%nat) -> getr R (reg 24) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 25) = Z_to_bv 64 (V 50%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 312) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 33%nat) + 400) -> L5.writable RSEGS M ((V 33%nat) + 392) 24 -> 4136 <= bv_unsigned (getr R (reg 10)) <= 140737488355327 -> bv_unsigned (getr R (reg 10)) mod 8 = 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> ~ (((V 33%nat) + 400) <= bv_unsigned a < ((V 33%nat) + 400) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> ~ (((V 33%nat) + 400) <= i < ((V 33%nat) + 400) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaebb4 M) (st fx' R' 0xaec80 M')
        /\ (forall x, In x KS_abdT -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 72%nat)
        /\ L5.u8_at RSEGS M' (V 51%nat) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 400) (bv_unsigned (getr R (reg 10)))
        /\ L5.defined M' ((V 50%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G18 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI20 K4 K5 pvzI21 K7 K8 K9 K10 K11 K12 K13 pvzI22 K15 K16 K17 K18 K19 K20 pvzI23 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV60l; move HV60l before pvzI7; pose proof (proj2 pvzI7) as HV60r; move HV60r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV61l; move HV61l before pvzI8; pose proof (proj2 pvzI8) as HV61r; move HV61r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV62l; move HV62l before pvzI9; pose proof (proj2 pvzI9) as HV62r; move HV62r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV63l; move HV63l before pvzI10; pose proof (proj2 pvzI10) as HV63r; move HV63r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV69l; move HV69l before pvzI16; pose proof (proj2 pvzI16) as HV69r; move HV69r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV70l; move HV70l before pvzI17; pose proof (proj2 pvzI17) as HV70r; move HV70r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV71l; move HV71l before pvzI18; pose proof (proj2 pvzI18) as HV71r; move HV71r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV72l; move HV72l before pvzI19; pose proof (proj2 pvzI19) as HV72r; move HV72r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K6l; move K6l before pvzI21; pose proof (proj2 pvzI21) as K6r; move K6r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K14l; move K14l before pvzI22; pose proof (proj2 pvzI22) as K14r; move K14r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K21l; move K21l before pvzI23; pose proof (proj2 pvzI23) as K21r; move K21r before pvzI23; clear pvzI23.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PabdT.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabdT.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabdT.kn0).
  { unfold know_ok, PabdT.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [cbn [edenot ev]; reflexivity | exact K46]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [cbn [edenot ev]; reflexivity | clear; lia | exact K47]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabdT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabdT.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> ~ ((vz_33 + 400) <= bv_unsigned a < (vz_33 + 400) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PabdT.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabdT.ps0) with 0xaec80 in Hms. change (SR.ps_regs PabdT.ps0) with (map (fun i => (i, nth i PabdT.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabdT.ps0) with PabdT.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabdT.regs0 PabdT.regs_out0 80 KS_abdT KS_abdT_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabdT.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabdT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdT.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PabdT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdT.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PabdT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdT.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PabdT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdT.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabdT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdT.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PabdT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdT.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PabdT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdT.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PabdT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdT.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PabdT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdT.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PabdT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdT.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PabdT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdT.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PabdT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdT.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PabdT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdT.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PabdT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdT.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PabdT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabdE4 := LibSegBa_abdE4_b.
Definition KS_abdE4 : list nat := Eval vm_compute in (BG.kept_list 80 PabdE4.regs0 PabdE4.regs_out0).
Lemma KS_abdE4_ok : BG.kept_ok 80 PabdE4.regs0 PabdE4.regs_out0 KS_abdE4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma abdE4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 33%nat) + 400) / 8) -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 34%nat) -> getr R (reg 25) = Z_to_bv 64 (V 50%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 312) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> L5.writable RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaec90 M) (st fx' R' 0xaec80 M')
        /\ (forall x, In x KS_abdE4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 72%nat)
        /\ L5.u8_at RSEGS M' (V 51%nat) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 0
        /\ L5.defined M' ((V 50%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G18 G19 G20 G21 G22 G23 G25 G26 G27 K0 K1 K2 pvzI20 K4 K5 pvzI21 K7 K8 K9 K10 K11 K12 K13 pvzI22 K15 K16 K17 K18 K19 K20 pvzI23 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV60l; move HV60l before pvzI7; pose proof (proj2 pvzI7) as HV60r; move HV60r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV61l; move HV61l before pvzI8; pose proof (proj2 pvzI8) as HV61r; move HV61r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV62l; move HV62l before pvzI9; pose proof (proj2 pvzI9) as HV62r; move HV62r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV63l; move HV63l before pvzI10; pose proof (proj2 pvzI10) as HV63r; move HV63r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV69l; move HV69l before pvzI16; pose proof (proj2 pvzI16) as HV69r; move HV69r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV70l; move HV70l before pvzI17; pose proof (proj2 pvzI17) as HV70r; move HV70r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV71l; move HV71l before pvzI18; pose proof (proj2 pvzI18) as HV71r; move HV71r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV72l; move HV72l before pvzI19; pose proof (proj2 pvzI19) as HV72r; move HV72r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K6l; move K6l before pvzI21; pose proof (proj2 pvzI21) as K6r; move K6r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K14l; move K14l before pvzI22; pose proof (proj2 pvzI22) as K14r; move K14r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K21l; move K21l before pvzI23; pose proof (proj2 pvzI23) as K21r; move K21r before pvzI23; clear pvzI23.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PabdE4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabdE4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabdE4.kn0).
  { unfold know_ok, PabdE4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabdE4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabdE4.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PabdE4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabdE4.ps0) with 0xaec80 in Hms. change (SR.ps_regs PabdE4.ps0) with (map (fun i => (i, nth i PabdE4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabdE4.ps0) with PabdE4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabdE4.regs0 PabdE4.regs_out0 80 KS_abdE4 KS_abdE4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE4.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PabdE4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PabdE1 := LibSegBa_abdE1_b.
Definition KS_abdE1 : list nat := Eval vm_compute in (BG.kept_list 80 PabdE1.regs0 PabdE1.regs_out0).
Lemma KS_abdE1_ok : BG.kept_ok 80 PabdE1.regs0 PabdE1.regs_out0 KS_abdE1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma abdE1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 4 -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 50%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 34%nat) -> getr R (reg 24) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 25) = Z_to_bv 64 (V 50%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 312) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> L5.writable RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaecb8 M) (st fx' R' 0xaec80 M')
        /\ (forall x, In x KS_abdE1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 63%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 72%nat)
        /\ L5.u8_at RSEGS M' (V 51%nat) 0
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 50%nat) 1172321806
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 8) 0
        /\ L5.defined M' ((V 50%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI20 K4 K5 pvzI21 K7 K8 K9 K10 K11 K12 K13 pvzI22 K15 K16 K17 K18 K19 K20 pvzI23 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV60l; move HV60l before pvzI7; pose proof (proj2 pvzI7) as HV60r; move HV60r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV61l; move HV61l before pvzI8; pose proof (proj2 pvzI8) as HV61r; move HV61r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV62l; move HV62l before pvzI9; pose proof (proj2 pvzI9) as HV62r; move HV62r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV63l; move HV63l before pvzI10; pose proof (proj2 pvzI10) as HV63r; move HV63r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV69l; move HV69l before pvzI16; pose proof (proj2 pvzI16) as HV69r; move HV69r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV70l; move HV70l before pvzI17; pose proof (proj2 pvzI17) as HV70r; move HV70r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV71l; move HV71l before pvzI18; pose proof (proj2 pvzI18) as HV71r; move HV71r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV72l; move HV72l before pvzI19; pose proof (proj2 pvzI19) as HV72r; move HV72r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K6l; move K6l before pvzI21; pose proof (proj2 pvzI21) as K6r; move K6r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K14l; move K14l before pvzI22; pose proof (proj2 pvzI22) as K14r; move K14r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K21l; move K21l before pvzI23; pose proof (proj2 pvzI23) as K21r; move K21r before pvzI23; clear pvzI23.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PabdE1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabdE1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabdE1.kn0).
  { unfold know_ok, PabdE1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | clear - HV2l HV2r K3l K3r K13 K25 K26; lia | exactA K44]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabdE1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabdE1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PabdE1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabdE1.ps0) with 0xaec80 in Hms. change (SR.ps_regs PabdE1.ps0) with (map (fun i => (i, nth i PabdE1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabdE1.ps0) with PabdE1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabdE1.regs0 PabdE1.regs_out0 80 KS_abdE1 KS_abdE1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdE1.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PabdE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

Module PabdU := LibSegBa_abdU_b.
Definition KS_abdU : list nat := Eval vm_compute in (BG.kept_list 80 PabdU.regs0 PabdU.regs_out0).
Lemma KS_abdU_ok : BG.kept_ok 80 PabdU.regs0 PabdU.regs_out0 KS_abdU = true. Proof. vm_compute. reflexivity. Qed.
Lemma abdU_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 224) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 116) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 50%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 (V 34%nat) -> getr R (reg 24) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 25) = Z_to_bv 64 (V 50%nat) -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 224) 224 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 10) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 33%nat) + 312) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 224) + 224 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 224)) -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 ->
  L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 ->
  L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) ->
  ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 224) + 224 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 224)) -> (((V 2%nat) - 224) + 224 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 224)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) ->
  ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) -> 6905856 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 8 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> (((V 2%nat) - 224) + 224 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 224)) -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) ->
  ((V 50%nat) + 64 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 50%nat)) -> ((V 51%nat) + 1 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 51%nat)) -> L5.u64_at RSEGS M (V 34%nat) 1251456 -> L5KA.zeros_at M 2147607320 1 ->
  ((((V 34%nat) / 8) + 2147450880) + 1 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 34%nat) / 8) + 2147450880)) -> L5.u32_at RSEGS M ((V 50%nat) + 32) (V 46%nat) -> 0 <= (V 46%nat) <= 4294967295 -> L5.writable RSEGS M ((V 33%nat) + 8) 1 ->
  L5.u8_at RSEGS M ((V 33%nat) + 10) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 392) (V 41%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 400) ((V 41%nat) + (V 42%nat)) -> L5.u64_at RSEGS M ((V 33%nat) + 408) ((V 41%nat) + (V 43%nat)) ->
  4096 <= (V 41%nat) <= 140737488314328 -> aligned (V 41%nat) 8 -> 40 <= (V 42%nat) <= 41000 -> aligned (V 42%nat) 8 ->
  40 <= (V 43%nat) <= 81920 -> aligned (V 43%nat) 8 -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((V 33%nat) + 392) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 33%nat) + 400) ->
  L5.u64_at RSEGS M ((V 2%nat) - 208) (((V 41%nat) + (V 42%nat)) + 40) -> L5.u64_at RSEGS M ((V 2%nat) - 216) ((V 41%nat) + (V 42%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 224) ((V 33%nat) + 392) -> L5.u64_at RSEGS M ((V 2%nat) - 200) ((V 41%nat) + (V 42%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 192) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) ((V 2%nat) - 160) -> L5.u64_at RSEGS M ((V 2%nat) - 176) (V 2%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 715660 ->
  (((V 41%nat) + (V 42%nat)) mod 2 ^ 64) < (((V 41%nat) + (V 43%nat)) mod 2 ^ 64) -> L5.u32_at RSEGS M ((V 2%nat) - 120) 2 -> L5.u64_at RSEGS M ((V 2%nat) - 112) 4 -> L5.u8_at RSEGS M ((V 33%nat) + 8) 1 ->
  L5KA.zeros_at M ((((V 2%nat) - 120) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 2%nat) - 116) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 2%nat) - 112) / 8) + 2147450880) 1 -> L5.writable RSEGS M ((V 2%nat) - 240) 240 ->
  L5KA.zeros_at M ((((V 2%nat) - 224) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 2%nat) - 216) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 2%nat) - 208) / 8) + 2147450880) 1 -> (((V 2%nat) - 240) + 240 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 240)) ->
  (((V 2%nat) - 240) + 240 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 240)) -> (((V 2%nat) - 240) + 240 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 240)) -> (((V 2%nat) - 240) + 240 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 240)) -> L5.writable RSEGS M ((V 33%nat) + 392) 24 ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> 4136 <= (((V 41%nat) + (V 42%nat)) + 40) <= 140737488355327 -> aligned (((V 41%nat) + (V 42%nat)) + 40) 8 ->
  (65536 + 6840320 <= ((V 41%nat) + (V 42%nat)) \/ ((V 41%nat) + (V 42%nat)) + 40 <= 65536) -> 4136 <= ((V 41%nat) + (V 42%nat)) <= 140737488355287 -> L5.writable RSEGS M ((V 41%nat) + (V 42%nat)) 40 -> L5KA.zeros_at M ((((V 41%nat) + (V 42%nat)) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M (((((V 41%nat) + (V 42%nat)) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M (((((V 41%nat) + (V 42%nat)) + 16) / 8) + 2147450880) 1 -> L5KA.zeros_at M (((((V 41%nat) + (V 42%nat)) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M (((((V 41%nat) + (V 42%nat)) + 32) / 8) + 2147450880) 1 ->
  (2147446784 + 17592186048512 <= ((V 41%nat) + (V 42%nat)) \/ ((V 41%nat) + (V 42%nat)) + 40 <= 2147446784) -> (((V 2%nat) - 240) + 240 <= ((V 41%nat) + (V 42%nat)) \/ ((V 41%nat) + (V 42%nat)) + 40 <= ((V 2%nat) - 240)) -> ((V 33%nat) + 416 <= ((V 41%nat) + (V 42%nat)) \/ ((V 41%nat) + (V 42%nat)) + 40 <= (V 33%nat)) -> ((V 50%nat) + 64 <= ((V 41%nat) + (V 42%nat)) \/ ((V 41%nat) + (V 42%nat)) + 40 <= (V 50%nat)) ->
  ((V 51%nat) + 1 <= ((V 41%nat) + (V 42%nat)) \/ ((V 41%nat) + (V 42%nat)) + 40 <= (V 51%nat)) -> ((V 34%nat) + 8 <= ((V 41%nat) + (V 42%nat)) \/ ((V 41%nat) + (V 42%nat)) + 40 <= (V 34%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 41%nat) + (V 42%nat)) + 0) <= bv_unsigned a < (((V 41%nat) + (V 42%nat)) + 0) + 40) -> ~ (((V 33%nat) + 400) <= bv_unsigned a < ((V 33%nat) + 400) + 8) -> ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 41%nat) + (V 42%nat)) + 0) <= i < (((V 41%nat) + (V 42%nat)) + 0) + 40) -> ~ (((V 33%nat) + 400) <= i < ((V 33%nat) + 400) + 8) -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb25f4 M) (st fx' R' 0xaebb4 M')
        /\ (forall x, In x KS_abdU -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 715660
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 41%nat) + (V 42%nat)) + 40)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 41%nat) + (V 42%nat)) + 40)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 41%nat) + (V 42%nat)) + 40)
        /\ getr R' (reg 14) = Z_to_bv 64 2147450880
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 41%nat) + (V 42%nat))
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 400) (((V 41%nat) + (V 42%nat)) + 40)
        /\ L5.u64_at RSEGS M' (((V 41%nat) + (V 42%nat)) + 32) 0
        /\ L5.u8_at RSEGS M' (((V 41%nat) + (V 42%nat)) + 24) 0
        /\ L5.u64_at RSEGS M' (((V 41%nat) + (V 42%nat)) + 16) 4
        /\ L5.u32_at RSEGS M' ((V 41%nat) + (V 42%nat)) 2).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 pvzI22 pvzI23 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI24 K4 K5 pvzI25 K7 K8 K9 K10 K11 K12 K13 pvzI26 K15 K16 K17 K18 K19 K20 pvzI27 K22 K23 K24 K25 K26 K27 K28 K29 pvzI28 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 pvzI29 K43 K44 K45 K46 K47 pvzI30 K49 pvzI31 K51 pvzI32 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70 K71 K72 K73 K74 K75 K76 K77 K78 K79 K80 K81 K82 K83 K84 K85 K86 K87 K88 K89 K90 K91 K92 K93 K94 K95 K96 K97 pvzI33 K99 K100 pvzI34 K102 K103 K104 K105 K106 K107 K108 K109 K110 K111 K112 K113.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV41l; move HV41l before pvzI5; pose proof (proj2 pvzI5) as HV41r; move HV41r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV60l; move HV60l before pvzI11; pose proof (proj2 pvzI11) as HV60r; move HV60r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV61l; move HV61l before pvzI12; pose proof (proj2 pvzI12) as HV61r; move HV61r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV62l; move HV62l before pvzI13; pose proof (proj2 pvzI13) as HV62r; move HV62r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV63l; move HV63l before pvzI14; pose proof (proj2 pvzI14) as HV63r; move HV63r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV64l; move HV64l before pvzI15; pose proof (proj2 pvzI15) as HV64r; move HV64r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV65l; move HV65l before pvzI16; pose proof (proj2 pvzI16) as HV65r; move HV65r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV66l; move HV66l before pvzI17; pose proof (proj2 pvzI17) as HV66r; move HV66r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV67l; move HV67l before pvzI18; pose proof (proj2 pvzI18) as HV67r; move HV67r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV68l; move HV68l before pvzI19; pose proof (proj2 pvzI19) as HV68r; move HV68r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV69l; move HV69l before pvzI20; pose proof (proj2 pvzI20) as HV69r; move HV69r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV70l; move HV70l before pvzI21; pose proof (proj2 pvzI21) as HV70r; move HV70r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as HV71l; move HV71l before pvzI22; pose proof (proj2 pvzI22) as HV71r; move HV71r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as HV72l; move HV72l before pvzI23; pose proof (proj2 pvzI23) as HV72r; move HV72r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K3l; move K3l before pvzI24; pose proof (proj2 pvzI24) as K3r; move K3r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K6l; move K6l before pvzI25; pose proof (proj2 pvzI25) as K6r; move K6r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K14l; move K14l before pvzI26; pose proof (proj2 pvzI26) as K14r; move K14r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K21l; move K21l before pvzI27; pose proof (proj2 pvzI27) as K21r; move K21r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K30l; move K30l before pvzI28; pose proof (proj2 pvzI28) as K30r; move K30r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K42l; move K42l before pvzI29; pose proof (proj2 pvzI29) as K42r; move K42r before pvzI29; clear pvzI29. pose proof (proj1 pvzI30) as K48l; move K48l before pvzI30; pose proof (proj2 pvzI30) as K48r; move K48r before pvzI30; clear pvzI30. pose proof (proj1 pvzI31) as K50l; move K50l before pvzI31; pose proof (proj2 pvzI31) as K50r; move K50r before pvzI31; clear pvzI31. pose proof (proj1 pvzI32) as K52l; move K52l before pvzI32; pose proof (proj2 pvzI32) as K52r; move K52r before pvzI32; clear pvzI32. pose proof (proj1 pvzI33) as K98l; move K98l before pvzI33; pose proof (proj2 pvzI33) as K98r; move K98r before pvzI33; clear pvzI33. pose proof (proj1 pvzI34) as K101l; move K101l before pvzI34; pose proof (proj2 pvzI34) as K101r; move K101r before pvzI34; clear pvzI34.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 46%nat => vz_46 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PabdU.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PabdU.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PabdU.kn0).
  { unfold know_ok, PabdU.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | exactA K10]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K77 K97 K112) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K77 K97 K112) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K77 K97 K112) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K77 K97 K112; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K77 K97 K112; lia | clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K77 K97 K112; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K77 K97 K112) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K77 K97 K112) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K77 K97 K112) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K77 K97 K112) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113) | exact (conj K30l K30r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113; lia | clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113; lia | clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K77 K97 K112) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113; lia | clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113; lia | exactA K38]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | evalEk ZA ltac:(clear - HV46l HV46r K42l K42r) | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111; lia | clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | byte_tac ltac:(clear) | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV43l HV43r K52l K52r) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113) | exact (conj K48l K48r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113) | clear; lia | exact K49]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K50l K50r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113) | exact (conj K50l K50r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K50l K50r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113) | clear; lia | exact K51]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K52l K52r) | exact (conj K52l K52r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV43l HV43r K52l K52r) | clear; lia | exact K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | generalize K64; match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | byte_tac ltac:(clear) | exactA K67]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K68]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K69]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K70]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K71]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K72]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K73]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K74]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | generalize K75; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | evalEk ZA ltac:(clear) | generalize K76; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K77 K97 K112) | evalEk ZA ltac:(clear) | generalize K77; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113) | evalEk ZA ltac:(clear) | generalize K78; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110; lia | exactA K79]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K80]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K81]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K82]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K83]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K84]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K85]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K86]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K87]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K88]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K89]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K90]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K91]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K92]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K93]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109; lia | exactA K94]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | generalize K95; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | evalEk ZA ltac:(clear) | generalize K96; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K77 K97 K112) | evalEk ZA ltac:(clear) | generalize K97; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | exact (conj K98l K98r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | clear; lia | exact K99]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk ZA ltac:(clear) | generalize K100; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | exact (conj K101l K101r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | exactA K102]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | exactA K103]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | exactA K104]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | exactA K105]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | exactA K106]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r; lia | exactA K107]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk ZA ltac:(clear) | generalize K108; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk ZA ltac:(clear) | generalize K109; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk ZA ltac:(clear) | generalize K110; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K14l K14r K18 K24 K25 K27 K29 K36 K40 K76 K96 K111) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk ZA ltac:(clear) | generalize K111; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K21l K21r K23 K24 K26 K28 K37 K77 K97 K112) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk ZA ltac:(clear) | generalize K112; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K30l K30r K32 K34 K35 K36 K37 K40 K78 K113) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk ZA ltac:(clear) | generalize K113; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PabdU.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PabdU.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((vz_41 + vz_42) + 0) <= bv_unsigned a < ((vz_41 + vz_42) + 0) + 40) -> ~ ((vz_33 + 400) <= bv_unsigned a < (vz_33 + 400) + 8) -> ~ ((vz_2 - 240) <= bv_unsigned a < (vz_2 - 240) + 80) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PabdU.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk' ZA Hag ltac:(clear) | clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K13 K25 K26 K34 K75 K76 K77 K78 K95 K96 K97 K109 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PabdU.ps0) with 0xaebb4 in Hms. change (SR.ps_regs PabdU.ps0) with (map (fun i => (i, nth i PabdU.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PabdU.ps0) with PabdU.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PabdU.regs0 PabdU.regs_out0 80 KS_abdU KS_abdU_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PabdU.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PabdU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdU.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PabdU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdU.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PabdU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdU.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PabdU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdU.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PabdU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdU.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PabdU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdU.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PabdU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdU.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PabdU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdU.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PabdU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdU.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PabdU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdU.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PabdU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PabdU.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PabdU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K13 K27 K28 K29 K35 K75 K95 K110) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV41l HV41r K48l K48r K98l K98r K101l K101r K100 K108 K109 K110 K111 K112 K113 HV42l HV42r K50l K50r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

End PNABDP.
