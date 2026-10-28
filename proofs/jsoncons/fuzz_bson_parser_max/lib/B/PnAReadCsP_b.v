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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_acsA_b LibSegBa_acsB_b LibSegBa_acsR_b LibSegBa_acsL_b LibSegBa_acsS_b LibSegBa_acsK0_b LibSegBa_acsKc_b LibSegBa_acsKz_b LibSegBa_acsP_b LibSegBa_acsE_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNACSP.
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
Module PacsA := LibSegBa_acsA_b.
Definition KS_acsA : list nat := Eval vm_compute in (BG.kept_list 80 PacsA.regs0 PacsA.regs_out0).
Lemma KS_acsA_ok : BG.kept_ok 80 PacsA.regs0 PacsA.regs_out0 KS_acsA = true. Proof. vm_compute. reflexivity. Qed.
Lemma acsA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 35%nat) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2cd0 M) (st fx' R' 0x5dc2c M')
        /\ (forall x, In x KS_acsA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 732488
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 10) = Z_to_bv 64 64
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 34%nat)
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
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PacsA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PacsA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PacsA.kn0).
  { unfold know_ok, PacsA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PacsA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PacsA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 160) <= bv_unsigned a < (vz_2 - 160) + 160) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PacsA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PacsA.ps0) with 0x5dc2c in Hms. change (SR.ps_regs PacsA.ps0) with (map (fun i => (i, nth i PacsA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PacsA.ps0) with PacsA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PacsA.regs0 PacsA.regs_out0 80 KS_acsA KS_acsA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PacsA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PacsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PacsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PacsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PacsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PacsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PacsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsA.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PacsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PacsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PacsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsA.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PacsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
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
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PacsB := LibSegBa_acsB_b.
Definition KS_acsB : list nat := Eval vm_compute in (BG.kept_list 80 PacsB.regs0 PacsB.regs_out0).
Lemma KS_acsB_ok : BG.kept_ok 80 PacsB.regs0 PacsB.regs_out0 KS_acsB = true. Proof. vm_compute. reflexivity. Qed.
Lemma acsB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 50%nat) <= 140737488355264 ->
  aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) ->
  L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 33%nat) <= 140737488354912 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 8) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 24) -> ~ (((V 50%nat) + 32) <= bv_unsigned a < ((V 50%nat) + 32) + 1) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 8) -> ~ (((V 2%nat) - 152) <= bv_unsigned a < ((V 2%nat) - 152) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 8) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 24) -> ~ (((V 50%nat) + 32) <= i < ((V 50%nat) + 32) + 1) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 8) -> ~ (((V 2%nat) - 152) <= i < ((V 2%nat) - 152) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2d48 M) (st fx' R' 0xaed4c M')
        /\ (forall x, In x KS_acsB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 732680
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 18) = Z_to_bv 64 40
        /\ getr R' (reg 19) = Z_to_bv 64 1
        /\ getr R' (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 33%nat) + 400)
        /\ getr R' (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 50%nat)
        /\ L5.u8_at RSEGS M' ((V 50%nat) + 32) 255
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 33%nat)
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450886) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450885) 243
        /\ L5.u8_at RSEGS M' (((V 50%nat) / 8) + 2147450884) 1
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) 732368
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) 115784
        /\ L5.u64_at RSEGS M' (V 50%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 50%nat)
        /\ L5.defined M' ((V 50%nat) + 24) 8
        /\ L5.defined M' ((V 50%nat) + 33) 31).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G20 G27 pvzI7 K1 K2 pvzI8 K4 K5 K6 K7 K8 K9 pvzI9 K11 K12 K13 K14 K15 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K10l; move K10l before pvzI9; pose proof (proj2 pvzI9) as K10r; move K10r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K16l; move K16l before pvzI10; pose proof (proj2 pvzI10) as K16r; move K16r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PacsB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PacsB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PacsB.kn0).
  { unfold know_ok, PacsB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | clear - HV2l HV2r K0l K0r K14 K15; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14; lia | clear - HV50l HV50r K3l K3r K7 K13 K14; lia | clear - HV50l HV50r K3l K3r K7 K13 K14; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14; lia | clear - HV50l HV50r K3l K3r K7 K13 K14; lia | clear - HV50l HV50r K3l K3r K7 K13 K14; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14; lia | clear - HV50l HV50r K3l K3r K7 K13 K14; lia | clear - HV50l HV50r K3l K3r K7 K13 K14; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15) | clear - HV50l HV50r K3l K3r K7 K13 K14; lia | clear - HV50l HV50r K3l K3r K7 K13 K14; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K10l K10r K12 K13 K15; lia | clear - HV51l HV51r K10l K10r K12 K13 K15; lia | clear - HV51l HV51r K10l K10r K12 K13 K15; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K10l K10r K12 K13 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PacsB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PacsB.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 8) -> ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 24) -> ~ ((vz_50 + 32) <= bv_unsigned a < (vz_50 + 32) + 1) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_2 - 136) <= bv_unsigned a < (vz_2 - 136) + 8) -> ~ ((vz_2 - 152) <= bv_unsigned a < (vz_2 - 152) + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5. apply Hfr. unfold PacsB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K7 K13 K14 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15 Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K15 Hn5; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PacsB.ps0) with 0xaed4c in Hms. change (SR.ps_regs PacsB.ps0) with (map (fun i => (i, nth i PacsB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PacsB.ps0) with PacsB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PacsB.regs0 PacsB.regs_out0 80 KS_acsB KS_acsB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PacsB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PacsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PacsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PacsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PacsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PacsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PacsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsB.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PacsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PacsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsB.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PacsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsB.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PacsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsB.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PacsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsB.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PacsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsB.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PacsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsB.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PacsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsB.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PacsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear - HV33l HV33r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K15) | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K7 K13 K14) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PacsR := LibSegBa_acsR_b.
Definition KS_acsR : list nat := Eval vm_compute in (BG.kept_list 80 PacsR.regs0 PacsR.regs_out0).
Lemma KS_acsR_ok : BG.kept_ok 80 PacsR.regs0 PacsR.regs_out0 KS_acsR = true. Proof. vm_compute. reflexivity. Qed.
Lemma acsR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 44%nat) -> getr R (reg 18) = Z_to_bv 64 40 -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
  0 <= (V 44%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2e08 M) (st fx' R' 0xb2e44 M')
        /\ (forall x, In x KS_acsR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) - 24)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 43%nat) + (V 44%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 pvzI12 K13 K14 K15 K16 K17 K18 pvzI13 K20 K21 K22 K23 K24 K25 K26 K27 K28 pvzI14 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 pvzI15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV51l; move HV51l before pvzI9; pose proof (proj2 pvzI9) as HV51r; move HV51r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K12l; move K12l before pvzI12; pose proof (proj2 pvzI12) as K12r; move K12r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K19l; move K19l before pvzI13; pose proof (proj2 pvzI13) as K19r; move K19r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K29l; move K29l before pvzI14; pose proof (proj2 pvzI14) as K29r; move K29r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K40l; move K40l before pvzI15; pose proof (proj2 pvzI15) as K40r; move K40r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PacsR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PacsR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PacsR.kn0).
  { unfold know_ok, PacsR.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K40l K40r) | exact (conj K40l K40r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PacsR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PacsR.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PacsR.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PacsR.ps0) with 0xb2e44 in Hms. change (SR.ps_regs PacsR.ps0) with (map (fun i => (i, nth i PacsR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PacsR.ps0) with PacsR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PacsR.regs0 PacsR.regs_out0 80 KS_acsR KS_acsR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PacsR.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PacsR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PacsR.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PacsR.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PacsL := LibSegBa_acsL_b.
Definition KS_acsL : list nat := Eval vm_compute in (BG.kept_list 80 PacsL.regs0 PacsL.regs_out0).
Lemma KS_acsL_ok : BG.kept_ok 80 PacsL.regs0 PacsL.regs_out0 KS_acsL = true. Proof. vm_compute. reflexivity. Qed.
Lemma acsL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 44%nat) -> getr R (reg 18) = Z_to_bv 64 40 -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
  0 <= (V 44%nat) <= 1 -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2e08 M) (st fx' R' 0xb2e44 M')
        /\ (forall x, In x KS_acsL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) - 24)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 43%nat) + (V 44%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 pvzI12 K13 K14 K15 K16 K17 K18 pvzI13 K20 K21 K22 K23 K24 K25 K26 K27 K28 pvzI14 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 pvzI15 K41 K42 K43 K44.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV51l; move HV51l before pvzI9; pose proof (proj2 pvzI9) as HV51r; move HV51r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K12l; move K12l before pvzI12; pose proof (proj2 pvzI12) as K12r; move K12r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K19l; move K19l before pvzI13; pose proof (proj2 pvzI13) as K19r; move K19r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K29l; move K29l before pvzI14; pose proof (proj2 pvzI14) as K29r; move K29r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K40l; move K40l before pvzI15; pose proof (proj2 pvzI15) as K40r; move K40r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PacsL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PacsL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PacsL.kn0).
  { unfold know_ok, PacsL.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K40l K40r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K36) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38) | clear - HV2l HV2r K3l K3r K11 K23 K24 K36; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K36; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K36) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K38) | clear - HV2l HV2r K3l K3r K11 K23 K24 K36; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K36; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K36) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K36; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K36; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K36) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K37) | clear - HV2l HV2r K3l K3r K11 K23 K24 K36; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K36; lia | exactA K44]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PacsL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PacsL.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PacsL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PacsL.ps0) with 0xb2e44 in Hms. change (SR.ps_regs PacsL.ps0) with (map (fun i => (i, nth i PacsL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PacsL.ps0) with PacsL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PacsL.regs0 PacsL.regs_out0 80 KS_acsL KS_acsL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PacsL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PacsL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PacsL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PacsL.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PacsS := LibSegBa_acsS_b.
Definition KS_acsS : list nat := Eval vm_compute in (BG.kept_list 80 PacsS.regs0 PacsS.regs_out0).
Lemma KS_acsS_ok : BG.kept_ok 80 PacsS.regs0 PacsS.regs_out0 KS_acsS = true. Proof. vm_compute. reflexivity. Qed.
Lemma acsS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 (V 44%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 42%nat) - 24) -> getr R (reg 12) = Z_to_bv 64 (V 46%nat) -> getr R (reg 18) = Z_to_bv 64 40 -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
  0 <= (V 44%nat) <= 1 -> 0 <= (V 46%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 42%nat) - 24) <= bv_unsigned a < ((V 42%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 42%nat) - 24) <= i < ((V 42%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2e44 M) (st fx' R' 0xb2e48 M')
        /\ (forall x, In x KS_acsS -> getr R' (reg x) = getr R (reg x))
        /\ L5.u64_at RSEGS M' ((V 42%nat) - 24) (V 46%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 pvzI12 K13 K14 K15 K16 K17 K18 pvzI13 K20 K21 K22 K23 K24 K25 K26 K27 K28 pvzI14 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 pvzI15 pvzI16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV42l; move HV42l before pvzI4; pose proof (proj2 pvzI4) as HV42r; move HV42r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV51l; move HV51l before pvzI9; pose proof (proj2 pvzI9) as HV51r; move HV51r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K12l; move K12l before pvzI12; pose proof (proj2 pvzI12) as K12r; move K12r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K19l; move K19l before pvzI13; pose proof (proj2 pvzI13) as K19r; move K19r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K29l; move K29l before pvzI14; pose proof (proj2 pvzI14) as K29r; move K29r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K40l; move K40l before pvzI15; pose proof (proj2 pvzI15) as K40r; move K40r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K41l; move K41l before pvzI16; pose proof (proj2 pvzI16) as K41r; move K41r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 46%nat => Z_to_bv 64 vz_46 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 46%nat => vz_46 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PacsS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PacsS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PacsS.kn0).
  { unfold know_ok, PacsS.kn0.
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
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K40l K40r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PacsS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PacsS.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_42 - 24) <= bv_unsigned a < (vz_42 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PacsS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | evalEk' ZA Hag ltac:(clear) | clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PacsS.ps0) with 0xb2e48 in Hms. change (SR.ps_regs PacsS.ps0) with (map (fun i => (i, nth i PacsS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PacsS.ps0) with PacsS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PacsS.regs0 PacsS.regs_out0 80 KS_acsS KS_acsS_ok HR Hag Hregs j Hj). }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV42l HV42r K29l K29r K30 K34 K36 K37 K38 K39) | evalEk' ZA Hag ltac:(clear - HV46l HV46r K41l K41r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PacsK0 := LibSegBa_acsK0_b.
Definition KS_acsK0 : list nat := Eval vm_compute in (BG.kept_list 80 PacsK0.regs0 PacsK0.regs_out0).
Lemma KS_acsK0_ok : BG.kept_ok 80 PacsK0.regs0 PacsK0.regs_out0 KS_acsK0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma acsK0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 0 -> getr R (reg 11) = Z_to_bv 64 ((V 42%nat) - 24) -> getr R (reg 18) = Z_to_bv 64 40 -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 -> (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) -> aligned (V 42%nat) 8 ->
  L5.u64_at RSEGS M ((V 42%nat) - 24) (V 43%nat) -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> L5KA.zeros_at M ((((V 42%nat) - 24) / 8) + 2147450880) 1 -> (((V 2%nat) - 160) + 160 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 160)) ->
  (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 136) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2e48 M) (st fx' R' 0xae848 M')
        /\ (forall x, In x KS_acsK0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 732780
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G10 G11 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI9 K4 K5 pvzI10 K7 K8 K9 K10 K11 pvzI11 K13 K14 K15 K16 K17 K18 pvzI12 K20 K21 K22 K23 K24 K25 K26 K27 K28 pvzI13 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K6l; move K6l before pvzI10; pose proof (proj2 pvzI10) as K6r; move K6r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K12l; move K12l before pvzI11; pose proof (proj2 pvzI11) as K12r; move K12r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K19l; move K19l before pvzI12; pose proof (proj2 pvzI12) as K19r; move K19r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K29l; move K29l before pvzI13; pose proof (proj2 pvzI13) as K29r; move K29r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 42%nat => vz_42 | 43%nat => vz_43 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PacsK0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PacsK0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PacsK0.kn0).
  { unfold know_ok, PacsK0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38; lia | clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38; lia | clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38; lia | clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K42]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PacsK0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PacsK0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PacsK0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PacsK0.ps0) with 0xae848 in Hms. change (SR.ps_regs PacsK0.ps0) with (map (fun i => (i, nth i PacsK0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PacsK0.ps0) with PacsK0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PacsK0.regs0 PacsK0.regs_out0 80 KS_acsK0 KS_acsK0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PacsK0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PacsK0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsK0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PacsK0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PacsK0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PacsK0.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PacsKc := LibSegBa_acsKc_b.
Definition KS_acsKc : list nat := Eval vm_compute in (BG.kept_list 80 PacsKc.regs0 PacsKc.regs_out0).
Lemma KS_acsKc_ok : BG.kept_ok 80 PacsKc.regs0 PacsKc.regs_out0 KS_acsKc = true. Proof. vm_compute. reflexivity. Qed.
Lemma acsKc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 11) = Z_to_bv 64 ((V 42%nat) - 24) -> getr R (reg 18) = Z_to_bv 64 40 -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 -> (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) -> aligned (V 42%nat) 8 ->
  L5.u64_at RSEGS M ((V 42%nat) - 24) (V 43%nat) -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> L5KA.zeros_at M ((((V 42%nat) - 24) / 8) + 2147450880) 1 -> (((V 2%nat) - 160) + 160 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 160)) ->
  (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) ->
  L5.u8_at RSEGS M ((V 50%nat) + 32) (V 45%nat) -> 1 <= (V 45%nat) <= 255 -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2e48 M) (st fx' R' 0xd5bc4 M')
        /\ (forall x, In x KS_acsKc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 732764
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 45%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G11 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 pvzI12 K13 K14 K15 K16 K17 K18 pvzI13 K20 K21 K22 K23 K24 K25 K26 K27 K28 pvzI14 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 pvzI15 K41 K42 K43 K44.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV45l; move HV45l before pvzI7; pose proof (proj2 pvzI7) as HV45r; move HV45r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV51l; move HV51l before pvzI9; pose proof (proj2 pvzI9) as HV51r; move HV51r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K12l; move K12l before pvzI12; pose proof (proj2 pvzI12) as K12r; move K12r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K19l; move K19l before pvzI13; pose proof (proj2 pvzI13) as K19r; move K19r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K29l; move K29l before pvzI14; pose proof (proj2 pvzI14) as K29r; move K29r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K40l; move K40l before pvzI15; pose proof (proj2 pvzI15) as K40r; move K40r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 45%nat => Z_to_bv 64 vz_45 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 42%nat => vz_42 | 43%nat => vz_43 | 45%nat => vz_45 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PacsKc.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PacsKc.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PacsKc.kn0).
  { unfold know_ok, PacsKc.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38; lia | clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38; lia | clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38; lia | clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear - HV45l HV45r K40l K40r) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | byte_tac ltac:(clear - HV45l HV45r K40l K40r) | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K40l K40r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K44]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PacsKc.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PacsKc.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PacsKc.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PacsKc.ps0) with 0xd5bc4 in Hms. change (SR.ps_regs PacsKc.ps0) with (map (fun i => (i, nth i PacsKc.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PacsKc.ps0) with PacsKc.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PacsKc.regs0 PacsKc.regs_out0 80 KS_acsKc KS_acsKc_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PacsKc.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PacsKc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKc.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PacsKc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PacsKc.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PacsKc.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PacsKz := LibSegBa_acsKz_b.
Definition KS_acsKz : list nat := Eval vm_compute in (BG.kept_list 80 PacsKz.regs0 PacsKz.regs_out0).
Lemma KS_acsKz_ok : BG.kept_ok 80 PacsKz.regs0 PacsKz.regs_out0 KS_acsKz = true. Proof. vm_compute. reflexivity. Qed.
Lemma acsKz_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 10) = Z_to_bv 64 1 -> getr R (reg 11) = Z_to_bv 64 ((V 42%nat) - 24) -> getr R (reg 18) = Z_to_bv 64 40 -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 -> L5.writable RSEGS M (V 50%nat) 64 ->
  (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) -> 4096 <= (V 51%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) -> (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) ->
  (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 400) (V 42%nat) -> 4136 <= (V 42%nat) <= 140737488355328 -> (65536 + 6840320 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 65536) -> aligned (V 42%nat) 8 ->
  L5.u64_at RSEGS M ((V 42%nat) - 24) (V 43%nat) -> (2147446784 + 17592186048512 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= 2147446784) -> L5KA.zeros_at M ((((V 42%nat) - 24) / 8) + 2147450880) 1 -> (((V 2%nat) - 160) + 160 <= ((V 42%nat) - 40) \/ ((V 42%nat) - 40) + 40 <= ((V 2%nat) - 160)) ->
  (((V 42%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 42%nat) - 40)) -> (((V 42%nat) - 40) + 40 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 42%nat) - 40)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) -> L5.u8_at RSEGS M ((V 50%nat) + 32) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) - 112) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 144) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2e48 M) (st fx' R' 0xb2f30 M')
        /\ (forall x, In x KS_acsKz -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 50%nat)
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
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 G2 G8 G9 G10 G11 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI22 K4 K5 pvzI23 K7 K8 K9 K10 K11 pvzI24 K13 K14 K15 K16 K17 K18 pvzI25 K20 K21 K22 K23 K24 K25 K26 K27 K28 pvzI26 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV50l; move HV50l before pvzI7; pose proof (proj2 pvzI7) as HV50r; move HV50r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV60l; move HV60l before pvzI9; pose proof (proj2 pvzI9) as HV60r; move HV60r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV61l; move HV61l before pvzI10; pose proof (proj2 pvzI10) as HV61r; move HV61r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV62l; move HV62l before pvzI11; pose proof (proj2 pvzI11) as HV62r; move HV62r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV63l; move HV63l before pvzI12; pose proof (proj2 pvzI12) as HV63r; move HV63r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV64l; move HV64l before pvzI13; pose proof (proj2 pvzI13) as HV64r; move HV64r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV65l; move HV65l before pvzI14; pose proof (proj2 pvzI14) as HV65r; move HV65r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV66l; move HV66l before pvzI15; pose proof (proj2 pvzI15) as HV66r; move HV66r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV67l; move HV67l before pvzI16; pose proof (proj2 pvzI16) as HV67r; move HV67r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV68l; move HV68l before pvzI17; pose proof (proj2 pvzI17) as HV68r; move HV68r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV69l; move HV69l before pvzI18; pose proof (proj2 pvzI18) as HV69r; move HV69r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV70l; move HV70l before pvzI19; pose proof (proj2 pvzI19) as HV70r; move HV70r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV71l; move HV71l before pvzI20; pose proof (proj2 pvzI20) as HV71r; move HV71r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV72l; move HV72l before pvzI21; pose proof (proj2 pvzI21) as HV72r; move HV72r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K3l; move K3l before pvzI22; pose proof (proj2 pvzI22) as K3r; move K3r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K6l; move K6l before pvzI23; pose proof (proj2 pvzI23) as K6r; move K6r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K12l; move K12l before pvzI24; pose proof (proj2 pvzI24) as K12r; move K12r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K19l; move K19l before pvzI25; pose proof (proj2 pvzI25) as K19r; move K19r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K29l; move K29l before pvzI26; pose proof (proj2 pvzI26) as K29r; move K29r before pvzI26; clear pvzI26.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 42%nat => vz_42 | 43%nat => vz_43 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PacsKz.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PacsKz.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PacsKz.kn0).
  { unfold know_ok, PacsKz.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38; lia | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | clear; lia | exact K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38; lia | clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38; lia | clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38; lia | clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K30 K33 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37; lia | byte_tac ltac:(clear) | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K23 K24 K35) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K25 K26 K27 K36) | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | clear - HV2l HV2r K3l K3r K11 K23 K24 K35; lia | exactA K56]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PacsKz.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PacsKz.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PacsKz.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PacsKz.ps0) with 0xb2f30 in Hms. change (SR.ps_regs PacsKz.ps0) with (map (fun i => (i, nth i PacsKz.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PacsKz.ps0) with PacsKz.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PacsKz.regs0 PacsKz.regs_out0 80 KS_acsKz KS_acsKz_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsKz.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PacsKz.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K19l K19r K21 K22 K24 K26 K38) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K12l K12r K16 K22 K23 K25 K27 K37) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PacsP := LibSegBa_acsP_b.
Definition KS_acsP : list nat := Eval vm_compute in (BG.kept_list 80 PacsP.regs0 PacsP.regs_out0).
Lemma KS_acsP_ok : BG.kept_ok 80 PacsP.regs0 PacsP.regs_out0 KS_acsP = true. Proof. vm_compute. reflexivity. Qed.
Lemma acsP_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 40 -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
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
    /\ (msteps RSEGS (st fx R 0xb2e5c M) (st fx' R' 0xaed4c M')
        /\ (forall x, In x KS_acsP -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 732680
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 12) = Z_to_bv 64 1).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 pvzI8 K13 K14 K15 K16 K17 K18 pvzI9 K20 K21 K22 K23 K24 K25 K26 K27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV51l; move HV51l before pvzI5; pose proof (proj2 pvzI5) as HV51r; move HV51r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K12l; move K12l before pvzI8; pose proof (proj2 pvzI8) as K12r; move K12r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K19l; move K19l before pvzI9; pose proof (proj2 pvzI9) as K19r; move K19r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PacsP.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PacsP.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PacsP.kn0).
  { unfold know_ok, PacsP.kn0.
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
  pvz_hg ltac:(idtac; destruct (PacsP.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PacsP.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PacsP.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PacsP.ps0) with 0xaed4c in Hms. change (SR.ps_regs PacsP.ps0) with (map (fun i => (i, nth i PacsP.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PacsP.ps0) with PacsP.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PacsP.regs0 PacsP.regs_out0 80 KS_acsP KS_acsP_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PacsP.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PacsP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsP.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PacsP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsP.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PacsP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PacsP.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PacsP.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PacsE := LibSegBa_acsE_b.
Definition KS_acsE : list nat := Eval vm_compute in (BG.kept_list 80 PacsE.regs0 PacsE.regs_out0).
Lemma KS_acsE_ok : BG.kept_ok 80 PacsE.regs0 PacsE.regs_out0 KS_acsE = true. Proof. vm_compute. reflexivity. Qed.
Lemma acsE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 160) -> getr R (reg 18) = Z_to_bv 64 40 -> getr R (reg 19) = Z_to_bv 64 1 -> getr R (reg 20) = Z_to_bv 64 (V 35%nat) -> getr R (reg 21) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 24) = Z_to_bv 64 ((V 33%nat) + 400) -> getr R (reg 25) = Z_to_bv 64 ((((V 33%nat) + 400) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487328 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 6905856 <= (V 33%nat) <= 140737488354912 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 416 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 2 -> L5KA.zeros_at M ((((V 33%nat) + 392) / 8) + 2147450880) 3 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 160)) ->
  L5.writable RSEGS M ((V 33%nat) + 8) 1 -> 6905856 <= (V 50%nat) <= 140737488355264 -> aligned (V 50%nat) 32 -> L5.defined M (V 50%nat) 64 ->
  L5.writable RSEGS M (V 50%nat) 64 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 64 <= 2147446784) -> L5.writable RSEGS M (((V 50%nat) / 8) + 2147450880) 8 -> L5.u64_at RSEGS M ((V 50%nat) + 56) (V 51%nat) ->
  4096 <= (V 51%nat) <= 140737488355327 -> L5.writable RSEGS M (V 51%nat) 1 -> (2147446784 + 17592186048512 <= (V 51%nat) \/ (V 51%nat) + 1 <= 2147446784) -> ((V 50%nat) + 64 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 50%nat)) ->
  (((V 2%nat) - 160) + 160 <= (V 50%nat) \/ (V 50%nat) + 64 <= ((V 2%nat) - 160)) -> (((V 2%nat) - 160) + 160 <= (V 51%nat) \/ (V 51%nat) + 1 <= ((V 2%nat) - 160)) -> ((V 33%nat) + 416 <= (V 50%nat) \/ (V 50%nat) + 64 <= (V 33%nat)) -> ((V 33%nat) + 416 <= (V 51%nat) \/ (V 51%nat) + 1 <= (V 33%nat)) ->
  ((((V 33%nat) / 8) + 2147450880) + 52 <= (((V 50%nat) / 8) + 2147450880) \/ (((V 50%nat) / 8) + 2147450880) + 8 <= (((V 33%nat) / 8) + 2147450880)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 61%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 62%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 63%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= bv_unsigned a < ((V 51%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 1) -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 8) -> ~ (((((V 50%nat) / 8) + 2147450880) + 0) <= i < ((((V 50%nat) / 8) + 2147450880) + 0) + 8) -> ~ (((V 51%nat) + 0) <= i < ((V 51%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2e6c M) (st fx' R' 0xb2f30 M')
        /\ (forall x, In x KS_acsE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 60%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 61%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 62%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 50%nat)
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
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI20 K4 K5 pvzI21 K7 K8 K9 K10 K11 K12 pvzI22 K14 K15 K16 K17 K18 K19 pvzI23 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV60l; move HV60l before pvzI7; pose proof (proj2 pvzI7) as HV60r; move HV60r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV61l; move HV61l before pvzI8; pose proof (proj2 pvzI8) as HV61r; move HV61r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV62l; move HV62l before pvzI9; pose proof (proj2 pvzI9) as HV62r; move HV62r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV63l; move HV63l before pvzI10; pose proof (proj2 pvzI10) as HV63r; move HV63r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV69l; move HV69l before pvzI16; pose proof (proj2 pvzI16) as HV69r; move HV69r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV70l; move HV70l before pvzI17; pose proof (proj2 pvzI17) as HV70r; move HV70r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV71l; move HV71l before pvzI18; pose proof (proj2 pvzI18) as HV71r; move HV71r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV72l; move HV72l before pvzI19; pose proof (proj2 pvzI19) as HV72r; move HV72r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K6l; move K6l before pvzI21; pose proof (proj2 pvzI21) as K6r; move K6r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K13l; move K13l before pvzI22; pose proof (proj2 pvzI22) as K13r; move K13r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K20l; move K20l before pvzI23; pose proof (proj2 pvzI23) as K20r; move K20r before pvzI23; clear pvzI23.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 50%nat => vz_50 | 51%nat => vz_51 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 73%nat. }
  assert (HR: regs_ok E PacsE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PacsE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PacsE.kn0).
  { unfold know_ok, PacsE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28; lia | exactA K9]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28; lia | clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28; lia | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27; lia | clear - HV51l HV51r K20l K20r K22 K23 K25 K27; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV61l HV61r) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV62l HV62r) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV63l HV63r) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K24 K25) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28) | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | clear - HV2l HV2r K3l K3r K11 K24 K25; lia | exactA K45]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PacsE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PacsE.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 8) <= bv_unsigned a < (vz_33 + 8) + 1) -> ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 8) -> ~ ((((vz_50 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_50 / 8) + 2147450880) + 0) + 8) -> ~ ((vz_51 + 0) <= bv_unsigned a < (vz_51 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PacsE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K20l K20r K22 K23 K25 K27 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PacsE.ps0) with 0xb2f30 in Hms. change (SR.ps_regs PacsE.ps0) with (map (fun i => (i, nth i PacsE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PacsE.ps0) with PacsE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PacsE.regs0 PacsE.regs_out0 80 KS_acsE KS_acsE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacsE.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PacsE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K20l K20r K22 K23 K25 K27) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K26 K27 K28) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K13l K13r K17 K23 K24 K26 K28) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PNACSP.
