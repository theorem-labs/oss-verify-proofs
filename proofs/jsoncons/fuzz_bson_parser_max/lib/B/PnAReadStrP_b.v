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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_arsA_b LibSegBa_arsB_b LibSegBa_arsRe_b LibSegBa_arsRz_b LibSegBa_arsRn_b LibSegBa_arsRp_b LibSegBa_arsS_b LibSegBa_arsQ_b LibSegBa_arsT0_b LibSegBa_arsU_b LibSegBa_arsW_b LibSegBa_arsV_b LibSegBa_arsE1_b LibSegBa_arsE5_b LibSegBa_arsEs_b LibSegBa_arsEc_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARSP.
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
Module ParsA := LibSegBa_arsA_b.
Definition KS_arsA : list nat := Eval vm_compute in (BG.kept_list 80 ParsA.regs0 ParsA.regs_out0).
Lemma KS_arsA_ok : BG.kept_ok 80 ParsA.regs0 ParsA.regs_out0 KS_arsA = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 36%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb343c M) (st fx' R' 0x5dc2c M')
        /\ (forall x, In x KS_arsA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 734384
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 2147450880
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
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 K0 K1 K2 pvzI4 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E ParsA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsA.kn0).
  { unfold know_ok, ParsA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 160) <= bv_unsigned a < (vz_2 - 160) + 160) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold ParsA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParsA.ps0) with 0x5dc2c in Hms. change (SR.ps_regs ParsA.ps0) with (map (fun i => (i, nth i ParsA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParsA.ps0) with ParsA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsA.regs0 ParsA.regs_out0 80 KS_arsA KS_arsA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParsA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth ParsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth ParsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth ParsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth ParsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth ParsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsA.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth ParsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
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
Module ParsB := LibSegBa_arsB_b.
Definition KS_arsB : list nat := Eval vm_compute in (BG.kept_list 80 ParsB.regs0 ParsB.regs_out0).
Lemma KS_arsB_ok : BG.kept_ok 80 ParsB.regs0 ParsB.regs_out0 KS_arsB = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 2147450880 ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 ->
  L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 8) -> ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 8) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 8) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 24) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb34b0 M) (st fx' R' 0xaed4c M')
        /\ (forall x, In x KS_arsB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 734560
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 4
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551602
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 22) = Z_to_bv 64 4
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 50%nat)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 242
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 4
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 2147450880
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) 734268
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) 87735
        /\ L5.u64_at RSEGS M' (V 50%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat)
        /\ L5.defined M' ((V 50%nat) + 24) 40).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G19 G20 G23 pvzI6 K1 K2 pvzI7 K4 pvzI8 K6 K7 K8 K9 K10 K11 pvzI9 K13 K14 K15 K16 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV51l; move HV51l before pvzI5; pose proof (proj2 pvzI5) as HV51r; move HV51r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K5l; move K5l before pvzI8; pose proof (proj2 pvzI8) as K5r; move K5r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E ParsB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsB.kn0).
  { unfold know_ok, ParsB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K17; lia | clear - HV2l HV2r K0l K0r K16 K17; lia | clear - HV2l HV2r K0l K0r K16 K17; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17) | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | clear - HV50l HV50r K5l K5r K9 K15 K16; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K12l K12r K14 K15 K17; lia | clear - HV51l HV51r K12l K12r K14 K15 K17; lia | clear - HV51l HV51r K12l K12r K14 K15 K17; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K12l K12r K14 K15 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsB.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 8) -> ~ ((vz_2 - 136) <= bv_unsigned a < (vz_2 - 136) + 8) -> ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 24) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold ParsB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K16 K17 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K5l K5r K9 K15 K16 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParsB.ps0) with 0xaed4c in Hms. change (SR.ps_regs ParsB.ps0) with (map (fun i => (i, nth i ParsB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParsB.ps0) with ParsB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsB.regs0 ParsB.regs_out0 80 KS_arsB KS_arsB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParsB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth ParsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth ParsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsB.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth ParsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsB.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth ParsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsB.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth ParsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsB.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth ParsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsB.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth ParsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsB.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth ParsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsB.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth ParsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K16 K17) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K5l K5r K9 K15 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParsRe := LibSegBa_arsRe_b.
Definition KS_arsRe : list nat := Eval vm_compute in (BG.kept_list 80 ParsRe.regs0 ParsRe.regs_out0).
Lemma KS_arsRe_ok : BG.kept_ok 80 ParsRe.regs0 ParsRe.regs_out0 KS_arsRe = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsRe_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  0 <= (V 40%nat) <= 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3560 M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_arsRe -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 734920
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G19 G20 G22 G24 G25 G26 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 pvzI9 K13 K14 K15 K16 K17 K18 pvzI10 K20 K21 K22 K23 K24 K25 K26 K27 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV40l; move HV40l before pvzI4; pose proof (proj2 pvzI4) as HV40r; move HV40r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K19l; move K19l before pvzI10; pose proof (proj2 pvzI10) as K19r; move K19r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K28l; move K28l before pvzI11; pose proof (proj2 pvzI11) as K28r; move K28r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 40%nat => Z_to_bv 64 vz_40 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 40%nat => vz_40 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E ParsRe.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsRe.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsRe.kn0).
  { unfold know_ok, ParsRe.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsRe.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsRe.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParsRe.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParsRe.ps0) with 0xae848 in Hms. change (SR.ps_regs ParsRe.ps0) with (map (fun i => (i, nth i ParsRe.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParsRe.ps0) with ParsRe.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsRe.regs0 ParsRe.regs_out0 80 KS_arsRe KS_arsRe_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParsRe.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParsRe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsRe.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParsRe.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParsRe.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParsRe.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParsRz := LibSegBa_arsRz_b.
Definition KS_arsRz : list nat := Eval vm_compute in (BG.kept_list 80 ParsRz.regs0 ParsRz.regs_out0).
Lemma KS_arsRz_ok : BG.kept_ok 80 ParsRz.regs0 ParsRz.regs_out0 KS_arsRz = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsRz_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 4 -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  L5.u32_at RSEGS M ((V 50%nat) + 32) (V 46%nat) -> 0 <= (V 46%nat) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3560 M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_arsRz -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 734968
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 5
        /\ getr R' (reg 27) = Z_to_bv 64 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G19 G20 G21 G22 G24 G25 G26 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 pvzI9 K13 K14 K15 K16 K17 K18 pvzI10 K20 K21 K22 K23 K24 K25 K26 K27 K28 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV46l; move HV46l before pvzI4; pose proof (proj2 pvzI4) as HV46r; move HV46r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K19l; move K19l before pvzI10; pose proof (proj2 pvzI10) as K19r; move K19r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K29l; move K29l before pvzI11; pose proof (proj2 pvzI11) as K29r; move K29r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 46%nat => Z_to_bv 64 vz_46 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 46%nat => vz_46 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E ParsRz.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsRz.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsRz.kn0).
  { unfold know_ok, ParsRz.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear - HV46l HV46r K29l K29r) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsRz.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsRz.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParsRz.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParsRz.ps0) with 0xae848 in Hms. change (SR.ps_regs ParsRz.ps0) with (map (fun i => (i, nth i ParsRz.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParsRz.ps0) with ParsRz.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsRz.regs0 ParsRz.regs_out0 80 KS_arsRz KS_arsRz_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParsRz.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParsRz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsRz.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParsRz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsRz.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParsRz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParsRz.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth ParsRz.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParsRn := LibSegBa_arsRn_b.
Definition KS_arsRn : list nat := Eval vm_compute in (BG.kept_list 80 ParsRn.regs0 ParsRn.regs_out0).
Lemma KS_arsRn_ok : BG.kept_ok 80 ParsRn.regs0 ParsRn.regs_out0 KS_arsRn = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsRn_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 4 -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  L5.u32_at RSEGS M ((V 50%nat) + 32) (V 46%nat) -> 2147483648 <= (V 46%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3560 M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_arsRn -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 734968
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 5).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G19 G20 G21 G22 G24 G25 G26 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 pvzI9 K13 K14 K15 K16 K17 K18 pvzI10 K20 K21 K22 K23 K24 K25 K26 K27 K28 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV46l; move HV46l before pvzI4; pose proof (proj2 pvzI4) as HV46r; move HV46r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K19l; move K19l before pvzI10; pose proof (proj2 pvzI10) as K19r; move K19r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K29l; move K29l before pvzI11; pose proof (proj2 pvzI11) as K29r; move K29r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 46%nat => Z_to_bv 64 vz_46 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 46%nat => vz_46 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E ParsRn.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsRn.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsRn.kn0).
  { unfold know_ok, ParsRn.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear - HV46l HV46r K29l K29r) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsRn.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsRn.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParsRn.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParsRn.ps0) with 0xae848 in Hms. change (SR.ps_regs ParsRn.ps0) with (map (fun i => (i, nth i ParsRn.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParsRn.ps0) with ParsRn.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsRn.regs0 ParsRn.regs_out0 80 KS_arsRn KS_arsRn_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParsRn.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParsRn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsRn.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParsRn.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParsRn.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParsRn.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParsRp := LibSegBa_arsRp_b.
Definition KS_arsRp : list nat := Eval vm_compute in (BG.kept_list 80 ParsRp.regs0 ParsRp.regs_out0).
Lemma KS_arsRp_ok : BG.kept_ok 80 ParsRp.regs0 ParsRp.regs_out0 KS_arsRp = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsRp_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 4 -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 22) = Z_to_bv 64 4 -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  L5.u32_at RSEGS M ((V 50%nat) + 32) (V 46%nat) -> 1 <= (V 46%nat) <= 2147483647 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3560 M) (st fx' R' 0xb4dc0 M')
        /\ (forall x, In x KS_arsRp -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 734592
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 46%nat) - 1)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 33%nat) + 368)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 46%nat) - 1)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 46%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G19 G20 G21 G22 G23 G24 G25 G26 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 pvzI9 K13 K14 K15 K16 K17 K18 pvzI10 K20 K21 K22 K23 K24 K25 K26 K27 K28 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV46l; move HV46l before pvzI4; pose proof (proj2 pvzI4) as HV46r; move HV46r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K19l; move K19l before pvzI10; pose proof (proj2 pvzI10) as K19r; move K19r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K29l; move K29l before pvzI11; pose proof (proj2 pvzI11) as K29r; move K29r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 46%nat => Z_to_bv 64 vz_46 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 46%nat => vz_46 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E ParsRp.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsRp.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsRp.kn0).
  { unfold know_ok, ParsRp.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear - HV46l HV46r K29l K29r) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsRp.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsRp.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParsRp.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParsRp.ps0) with 0xb4dc0 in Hms. change (SR.ps_regs ParsRp.ps0) with (map (fun i => (i, nth i ParsRp.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParsRp.ps0) with ParsRp.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsRp.regs0 ParsRp.regs_out0 80 KS_arsRp KS_arsRp_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParsRp.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParsRp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsRp.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParsRp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsRp.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParsRp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsRp.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParsRp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsRp.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth ParsRp.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParsRp.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth ParsRp.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParsS := LibSegBa_arsS_b.
Definition KS_arsS_0 : list nat := Eval vm_compute in (BG.kept_list 80 ParsS.regs0 ParsS.regs_out0).
Lemma KS_arsS_0_ok : BG.kept_ok 80 ParsS.regs0 ParsS.regs_out0 KS_arsS_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arsS_1 : list nat := Eval vm_compute in (BG.kept_list 80 ParsS.regs0 ParsS.regs_out1).
Lemma KS_arsS_1_ok : BG.kept_ok 80 ParsS.regs0 ParsS.regs_out1 KS_arsS_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 11) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 21) = Z_to_bv 64 (V 48%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  0 <= (V 47%nat) <= 2147483647 -> 0 <= (V 48%nat) <= 2147483647 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb3580 M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_arsS_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 735016
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ 1 <= (((V 47%nat) - (V 48%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb3580 M) (st fx' R' 0xb3584 M')
        /\ (forall x, In x KS_arsS_1 -> getr R' (reg x) = getr R (reg x))
        /\ (((V 47%nat) - (V 48%nat)) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G11 G19 G20 G21 G24 G25 G26 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 pvzI10 K13 K14 K15 K16 K17 K18 pvzI11 K20 K21 K22 K23 K24 K25 K26 K27 pvzI12 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K12l; move K12l before pvzI10; pose proof (proj2 pvzI10) as K12r; move K12r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K19l; move K19l before pvzI11; pose proof (proj2 pvzI11) as K19r; move K19r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K28l; move K28l before pvzI12; pose proof (proj2 pvzI12) as K28r; move K28r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K29l; move K29l before pvzI13; pose proof (proj2 pvzI13) as K29r; move K29r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E ParsS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsS.kn0).
  { unfold know_ok, ParsS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsS.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParsS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc ParsS.ps0) with 0xae848 in Hms. change (SR.ps_regs ParsS.ps0) with (map (fun i => (i, nth i ParsS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParsS.ps0) with ParsS.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsS.regs0 ParsS.regs_out0 80 KS_arsS_0 KS_arsS_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParsS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParsS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParsS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParsS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParsS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParsS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc ParsS.ps1) with 0xb3584 in Hms. change (SR.ps_regs ParsS.ps1) with (map (fun i => (i, nth i ParsS.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParsS.ps1) with ParsS.cells1 in Hcells. unfold ParsS.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsS.regs0 ParsS.regs_out1 80 KS_arsS_1 KS_arsS_1_ok HR Hag Hregs j Hj). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParsQ := LibSegBa_arsQ_b.
Definition KS_arsQ : list nat := Eval vm_compute in (BG.kept_list 80 ParsQ.regs0 ParsQ.regs_out0).
Lemma KS_arsQ_ok : BG.kept_ok 80 ParsQ.regs0 ParsQ.regs_out0 KS_arsQ = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsQ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 41%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 36%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 50%nat) / 8) + 2147450880) + 6) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 6) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 50%nat) / 8) + 2147450880) + 6) <= i < ((((V 50%nat) / 8) + 2147450880) + 6) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3584 M) (st fx' R' 0xaed4c M')
        /\ (forall x, In x KS_arsQ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 734628
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 48)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 1
        /\ getr R' (reg 22) = Z_to_bv 64 (V 36%nat)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G19 G20 G23 G24 G25 G26 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 pvzI9 K13 K14 K15 K16 K17 K18 pvzI10 K20 K21 K22 K23 K24 K25 K26 K27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K12l; move K12l before pvzI9; pose proof (proj2 pvzI9) as K12r; move K12r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K19l; move K19l before pvzI10; pose proof (proj2 pvzI10) as K19r; move K19r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 41%nat => Z_to_bv 64 vz_41 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 41%nat => vz_41 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E ParsQ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsQ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsQ.kn0).
  { unfold know_ok, ParsQ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsQ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsQ.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((vz_50 / 8) + 2147450880) + 6) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 6) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold ParsQ.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParsQ.ps0) with 0xaed4c in Hms. change (SR.ps_regs ParsQ.ps0) with (map (fun i => (i, nth i ParsQ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParsQ.ps0) with ParsQ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsQ.regs0 ParsQ.regs_out0 80 KS_arsQ KS_arsQ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParsQ.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParsQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsQ.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParsQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsQ.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParsQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsQ.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParsQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsQ.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth ParsQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsQ.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth ParsQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsQ.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth ParsQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParsT0 := LibSegBa_arsT0_b.
Definition KS_arsT0 : list nat := Eval vm_compute in (BG.kept_list 80 ParsT0.regs0 ParsT0.regs_out0).
Lemma KS_arsT0_ok : BG.kept_ok 80 ParsT0.regs0 ParsT0.regs_out0 KS_arsT0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsT0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 22) = Z_to_bv 64 (V 36%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb35a4 M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_arsT0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 735068
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G19 G20 G22 G24 G25 G26 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 pvzI8 K13 K14 K15 K16 K17 K18 pvzI9 K20 K21 K22 K23 K24 K25 K26 K27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV51l; move HV51l before pvzI5; pose proof (proj2 pvzI5) as HV51r; move HV51r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K12l; move K12l before pvzI8; pose proof (proj2 pvzI8) as K12r; move K12r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K19l; move K19l before pvzI9; pose proof (proj2 pvzI9) as K19r; move K19r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E ParsT0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsT0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsT0.kn0).
  { unfold know_ok, ParsT0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsT0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsT0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParsT0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParsT0.ps0) with 0xae848 in Hms. change (SR.ps_regs ParsT0.ps0) with (map (fun i => (i, nth i ParsT0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParsT0.ps0) with ParsT0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsT0.regs0 ParsT0.regs_out0 80 KS_arsT0 KS_arsT0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParsT0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParsT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsT0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParsT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParsT0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParsT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParsU := LibSegBa_arsU_b.
Definition KS_arsU : list nat := Eval vm_compute in (BG.kept_list 80 ParsU.regs0 ParsU.regs_out0).
Lemma KS_arsU_ok : BG.kept_ok 80 ParsU.regs0 ParsU.regs_out0 KS_arsU = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsU_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 18) = Z_to_bv 64 (V 41%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 1 -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 46%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) 2147450880 -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 -> (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) ->
  aligned (V 42%nat) 8 -> L5.u64_at RSEGS M ((V 42%nat) - 24) (V 43%nat) -> L5.writable RSEGS M ((V 42%nat) - 24) 8 -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) ->
  L5KA.zeros_at M ((((V 42%nat) - 24) / 8) + 2147450880) 1 -> (((V 2%nat) - 160) + 160 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 160)) -> (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 42%nat) - 40)) ->
  (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) -> 1 <= (V 46%nat) <= 2147483647 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb35a4 M) (st fx' R' 0xb3600 M')
        /\ (forall x, In x KS_arsU -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 42%nat) - 24)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 43%nat) + (V 46%nat)) + 4)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 ((V 46%nat) + 4)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G18 G19 G20 G24 G25 G26 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 pvzI11 K13 K14 K15 K16 K17 K18 pvzI12 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 pvzI13 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 pvzI14.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV41l; move HV41l before pvzI3; pose proof (proj2 pvzI3) as HV41r; move HV41r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV42l; move HV42l before pvzI4; pose proof (proj2 pvzI4) as HV42r; move HV42r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV46l; move HV46l before pvzI6; pose proof (proj2 pvzI6) as HV46r; move HV46r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K12l; move K12l before pvzI11; pose proof (proj2 pvzI11) as K12r; move K12r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K19l; move K19l before pvzI12; pose proof (proj2 pvzI12) as K19r; move K19r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K30l; move K30l before pvzI13; pose proof (proj2 pvzI13) as K30r; move K30r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K41l; move K41l before pvzI14; pose proof (proj2 pvzI14) as K41r; move K41r before pvzI14; clear pvzI14.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 46%nat => vz_46 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E ParsU.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsU.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsU.kn0).
  { unfold know_ok, ParsU.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K37) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K37) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K37) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24 K37; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K37; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K37; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K40) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K40) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K40) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K40; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K40; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K40; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K40) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K40) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K40) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K40) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K37) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24 K37; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K37; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38) | evalEk ZA ltac:(clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40) | exact (conj K30l K30r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40; lia | clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40; lia | clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40; lia | clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40; lia | clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40; lia | clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K38) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K30l K30r K31 K35 K37 K38 K39 K40) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K40) | evalEk ZA ltac:(clear) | generalize K40; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsU.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsU.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParsU.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParsU.ps0) with 0xb3600 in Hms. change (SR.ps_regs ParsU.ps0) with (map (fun i => (i, nth i ParsU.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParsU.ps0) with ParsU.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsU.regs0 ParsU.regs_out0 80 KS_arsU KS_arsU_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParsU.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParsU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsU.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParsU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsU.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParsU.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParsU.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth ParsU.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParsW := LibSegBa_arsW_b.
Definition KS_arsW : list nat := Eval vm_compute in (BG.kept_list 80 ParsW.regs0 ParsW.regs_out0).
Lemma KS_arsW_ok : BG.kept_ok 80 ParsW.regs0 ParsW.regs_out0 KS_arsW = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsW_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 ((V 42%nat) - 24) -> getr R (reg 11) = Z_to_bv 64 (V 49%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 -> (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) -> aligned (V 42%nat) 8 ->
  L5.u64_at RSEGS M ((V 42%nat) - 24) (V 43%nat) -> L5.writable RSEGS M ((V 42%nat) - 24) 8 -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> L5KA.zeros_at M ((((V 42%nat) - 24) / 8) + 2147450880) 1 ->
  (((V 2%nat) - 160) + 160 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 160)) -> (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) ->
  0 <= (V 49%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 42%nat) - 24) <= bv_unsigned a < ((V 42%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 42%nat) - 24) <= i < ((V 42%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3600 M) (st fx' R' 0xb3604 M')
        /\ (forall x, In x KS_arsW -> getr R' (reg x) = getr R (reg x))
        /\ L5.u64_at RSEGS M' ((V 42%nat) - 24) (V 49%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G11 G19 G24 G25 G26 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 pvzI10 K13 K14 K15 K16 K17 K18 pvzI11 K20 K21 K22 K23 K24 K25 K26 K27 K28 pvzI12 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV42l; move HV42l before pvzI3; pose proof (proj2 pvzI3) as HV42r; move HV42r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV49l; move HV49l before pvzI5; pose proof (proj2 pvzI5) as HV49r; move HV49r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K12l; move K12l before pvzI10; pose proof (proj2 pvzI10) as K12r; move K12r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K19l; move K19l before pvzI11; pose proof (proj2 pvzI11) as K19r; move K19r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K29l; move K29l before pvzI12; pose proof (proj2 pvzI12) as K29r; move K29r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K40l; move K40l before pvzI13; pose proof (proj2 pvzI13) as K40r; move K40r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 42%nat => vz_42 | 43%nat => vz_43 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E ParsW.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsW.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsW.kn0).
  { unfold know_ok, ParsW.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K36) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K36) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K36) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24 K36; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K36; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K36; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K39) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K39) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K39) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K39; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K39; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K39; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K39) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K39) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K39) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K39) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39; lia | clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39; lia | clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39; lia | clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39; lia | clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39; lia | clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV49l HV49r K40l K40r) | exact (conj K40l K40r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsW.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsW.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_42 - 24) <= bv_unsigned a < (vz_42 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold ParsW.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | evalEk' ZA Hag ltac:(clear) | clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParsW.ps0) with 0xb3604 in Hms. change (SR.ps_regs ParsW.ps0) with (map (fun i => (i, nth i ParsW.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParsW.ps0) with ParsW.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsW.regs0 ParsW.regs_out0 80 KS_arsW KS_arsW_ok HR Hag Hregs j Hj). }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | evalEk' ZA Hag ltac:(clear - HV49l HV49r K40l K40r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParsV := LibSegBa_arsV_b.
Definition KS_arsV : list nat := Eval vm_compute in (BG.kept_list 80 ParsV.regs0 ParsV.regs_out0).
Lemma KS_arsV_ok : BG.kept_ok 80 ParsV.regs0 ParsV.regs_out0 KS_arsV = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsV_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 12) = Z_to_bv 64 (V 41%nat) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 48%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3604 M) (st fx' R' 0xb36b8 M')
        /\ (forall x, In x KS_arsV -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 48%nat)
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
        /\ L5.defined M' ((V 50%nat) + 8) 56).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G12 G19 G21 G24 G25 G26 K0 K1 K2 pvzI20 K4 K5 pvzI21 K7 K8 K9 K10 K11 pvzI22 K13 K14 K15 K16 K17 K18 pvzI23 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV41l; move HV41l before pvzI3; pose proof (proj2 pvzI3) as HV41r; move HV41r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV48l; move HV48l before pvzI4; pose proof (proj2 pvzI4) as HV48r; move HV48r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV60l; move HV60l before pvzI7; pose proof (proj2 pvzI7) as HV60r; move HV60r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV61l; move HV61l before pvzI8; pose proof (proj2 pvzI8) as HV61r; move HV61r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV62l; move HV62l before pvzI9; pose proof (proj2 pvzI9) as HV62r; move HV62r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV63l; move HV63l before pvzI10; pose proof (proj2 pvzI10) as HV63r; move HV63r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV69l; move HV69l before pvzI16; pose proof (proj2 pvzI16) as HV69r; move HV69r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV70l; move HV70l before pvzI17; pose proof (proj2 pvzI17) as HV70r; move HV70r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV71l; move HV71l before pvzI18; pose proof (proj2 pvzI18) as HV71r; move HV71r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV72l; move HV72l before pvzI19; pose proof (proj2 pvzI19) as HV72r; move HV72r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K6l; move K6l before pvzI21; pose proof (proj2 pvzI21) as K6r; move K6r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K12l; move K12l before pvzI22; pose proof (proj2 pvzI22) as K12r; move K12r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K19l; move K19l before pvzI23; pose proof (proj2 pvzI23) as K19r; move K19r before pvzI23; clear pvzI23.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 41%nat => Z_to_bv 64 vz_41 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 41%nat => vz_41 | 48%nat => vz_48 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E ParsV.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsV.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsV.kn0).
  { unfold know_ok, ParsV.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K40]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsV.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsV.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold ParsV.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParsV.ps0) with 0xb36b8 in Hms. change (SR.ps_regs ParsV.ps0) with (map (fun i => (i, nth i ParsV.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParsV.ps0) with ParsV.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsV.regs0 ParsV.regs_out0 80 KS_arsV KS_arsV_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsV.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth ParsV.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParsE1 := LibSegBa_arsE1_b.
Definition KS_arsE1 : list nat := Eval vm_compute in (BG.kept_list 80 ParsE1.regs0 ParsE1.regs_out0).
Lemma KS_arsE1_ok : BG.kept_ok 80 ParsE1.regs0 ParsE1.regs_out0 KS_arsE1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsE1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) 2147450880 -> L5.writable RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb36c8 M) (st fx' R' 0xb36b8 M')
        /\ (forall x, In x KS_arsE1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
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
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G19 G24 G25 G26 K0 K1 K2 pvzI18 K4 K5 pvzI19 K7 K8 K9 K10 K11 pvzI20 K13 K14 K15 K16 K17 K18 pvzI21 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV50l; move HV50l before pvzI3; pose proof (proj2 pvzI3) as HV50r; move HV50r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV51l; move HV51l before pvzI4; pose proof (proj2 pvzI4) as HV51r; move HV51r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV69l; move HV69l before pvzI14; pose proof (proj2 pvzI14) as HV69r; move HV69r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV70l; move HV70l before pvzI15; pose proof (proj2 pvzI15) as HV70r; move HV70r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV71l; move HV71l before pvzI16; pose proof (proj2 pvzI16) as HV71r; move HV71r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV72l; move HV72l before pvzI17; pose proof (proj2 pvzI17) as HV72r; move HV72r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K3l; move K3l before pvzI18; pose proof (proj2 pvzI18) as K3r; move K3r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K6l; move K6l before pvzI19; pose proof (proj2 pvzI19) as K6r; move K6r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K12l; move K12l before pvzI20; pose proof (proj2 pvzI20) as K12r; move K12r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E ParsE1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsE1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsE1.kn0).
  { unfold know_ok, ParsE1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K42]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsE1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsE1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold ParsE1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParsE1.ps0) with 0xb36b8 in Hms. change (SR.ps_regs ParsE1.ps0) with (map (fun i => (i, nth i ParsE1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParsE1.ps0) with ParsE1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsE1.regs0 ParsE1.regs_out0 80 KS_arsE1 KS_arsE1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE1.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth ParsE1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParsE5 := LibSegBa_arsE5_b.
Definition KS_arsE5 : list nat := Eval vm_compute in (BG.kept_list 80 ParsE5.regs0 ParsE5.regs_out0).
Lemma KS_arsE5_ok : BG.kept_ok 80 ParsE5.regs0 ParsE5.regs_out0 KS_arsE5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsE5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) 2147450880 -> L5.writable RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb36f8 M) (st fx' R' 0xb36b8 M')
        /\ (forall x, In x KS_arsE5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
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
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G19 G24 G25 G26 K0 K1 K2 pvzI18 K4 K5 pvzI19 K7 K8 K9 K10 K11 pvzI20 K13 K14 K15 K16 K17 K18 pvzI21 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV50l; move HV50l before pvzI3; pose proof (proj2 pvzI3) as HV50r; move HV50r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV51l; move HV51l before pvzI4; pose proof (proj2 pvzI4) as HV51r; move HV51r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV69l; move HV69l before pvzI14; pose proof (proj2 pvzI14) as HV69r; move HV69r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV70l; move HV70l before pvzI15; pose proof (proj2 pvzI15) as HV70r; move HV70r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV71l; move HV71l before pvzI16; pose proof (proj2 pvzI16) as HV71r; move HV71r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV72l; move HV72l before pvzI17; pose proof (proj2 pvzI17) as HV72r; move HV72r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K3l; move K3l before pvzI18; pose proof (proj2 pvzI18) as K3r; move K3r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K6l; move K6l before pvzI19; pose proof (proj2 pvzI19) as K6r; move K6r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K12l; move K12l before pvzI20; pose proof (proj2 pvzI20) as K12r; move K12r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E ParsE5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsE5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsE5.kn0).
  { unfold know_ok, ParsE5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K42]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsE5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsE5.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold ParsE5.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParsE5.ps0) with 0xb36b8 in Hms. change (SR.ps_regs ParsE5.ps0) with (map (fun i => (i, nth i ParsE5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParsE5.ps0) with ParsE5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsE5.regs0 ParsE5.regs_out0 80 KS_arsE5 KS_arsE5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsE5.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth ParsE5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParsEs := LibSegBa_arsEs_b.
Definition KS_arsEs : list nat := Eval vm_compute in (BG.kept_list 80 ParsEs.regs0 ParsEs.regs_out0).
Lemma KS_arsEs_ok : BG.kept_ok 80 ParsEs.regs0 ParsEs.regs_out0 KS_arsEs = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsEs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) 2147450880 -> L5.writable RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb3728 M) (st fx' R' 0xb36b8 M')
        /\ (forall x, In x KS_arsEs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
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
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G19 G24 G25 G26 K0 K1 K2 pvzI18 K4 K5 pvzI19 K7 K8 K9 K10 K11 pvzI20 K13 K14 K15 K16 K17 K18 pvzI21 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV50l; move HV50l before pvzI3; pose proof (proj2 pvzI3) as HV50r; move HV50r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV51l; move HV51l before pvzI4; pose proof (proj2 pvzI4) as HV51r; move HV51r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV69l; move HV69l before pvzI14; pose proof (proj2 pvzI14) as HV69r; move HV69r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV70l; move HV70l before pvzI15; pose proof (proj2 pvzI15) as HV70r; move HV70r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV71l; move HV71l before pvzI16; pose proof (proj2 pvzI16) as HV71r; move HV71r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV72l; move HV72l before pvzI17; pose proof (proj2 pvzI17) as HV72r; move HV72r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K3l; move K3l before pvzI18; pose proof (proj2 pvzI18) as K3r; move K3r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K6l; move K6l before pvzI19; pose proof (proj2 pvzI19) as K6r; move K6r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K12l; move K12l before pvzI20; pose proof (proj2 pvzI20) as K12r; move K12r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E ParsEs.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsEs.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsEs.kn0).
  { unfold know_ok, ParsEs.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K42]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsEs.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsEs.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold ParsEs.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParsEs.ps0) with 0xb36b8 in Hms. change (SR.ps_regs ParsEs.ps0) with (map (fun i => (i, nth i ParsEs.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParsEs.ps0) with ParsEs.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsEs.regs0 ParsEs.regs_out0 80 KS_arsEs KS_arsEs_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEs.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth ParsEs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParsEc := LibSegBa_arsEc_b.
Definition KS_arsEc : list nat := Eval vm_compute in (BG.kept_list 80 ParsEc.regs0 ParsEc.regs_out0).
Lemma KS_arsEc_ok : BG.kept_ok 80 ParsEc.regs0 ParsEc.regs_out0 KS_arsEc = true. Proof. vm_compute. reflexivity. Qed.
Lemma arsEc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 19) = Z_to_bv 64 (V 33%nat) -> getr R (reg 24) = Z_to_bv 64 (V 50%nat) -> getr R (reg 25) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) 2147450880 -> L5.writable RSEGS M ((V 33%nat) + 8) 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb375c M) (st fx' R' 0xb36b8 M')
        /\ (forall x, In x KS_arsEc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
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
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 G2 G8 G9 G19 G24 G25 G26 K0 K1 K2 pvzI18 K4 K5 pvzI19 K7 K8 K9 K10 K11 pvzI20 K13 K14 K15 K16 K17 K18 pvzI21 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV50l; move HV50l before pvzI3; pose proof (proj2 pvzI3) as HV50r; move HV50r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV51l; move HV51l before pvzI4; pose proof (proj2 pvzI4) as HV51r; move HV51r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV69l; move HV69l before pvzI14; pose proof (proj2 pvzI14) as HV69r; move HV69r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV70l; move HV70l before pvzI15; pose proof (proj2 pvzI15) as HV70r; move HV70r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV71l; move HV71l before pvzI16; pose proof (proj2 pvzI16) as HV71r; move HV71r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV72l; move HV72l before pvzI17; pose proof (proj2 pvzI17) as HV72r; move HV72r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K3l; move K3l before pvzI18; pose proof (proj2 pvzI18) as K3r; move K3r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K6l; move K6l before pvzI19; pose proof (proj2 pvzI19) as K6r; move K6r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K12l; move K12l before pvzI20; pose proof (proj2 pvzI20) as K12r; move K12r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K19l; move K19l before pvzI21; pose proof (proj2 pvzI21) as K19r; move K19r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E ParsEc.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParsEc.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParsEc.kn0).
  { unfold know_ok, ParsEc.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | clear - HV2l HV2r K3l K3r K11 K23 K24; lia | exactA K42]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParsEc.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParsEc.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold ParsEc.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParsEc.ps0) with 0xb36b8 in Hms. change (SR.ps_regs ParsEc.ps0) with (map (fun i => (i, nth i ParsEc.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParsEc.ps0) with ParsEc.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParsEc.regs0 ParsEc.regs_out0 80 KS_arsEc KS_arsEc_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParsEc.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth ParsEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PNARSP.
