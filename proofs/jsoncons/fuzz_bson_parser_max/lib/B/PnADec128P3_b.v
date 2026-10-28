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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_adkRH_b LibSegBa_adkRF_b LibSegBa_adkL0_b LibSegBa_adkL1_b LibSegBa_adkL2_b LibSegBa_adkL3_b LibSegBa_adkRM_b LibSegBa_adkRMr_b LibSegBa_adkRT_b LibSegBa_adkRT0_b LibSegBa_adkRT0r_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADP3.
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
Module PadkRH := LibSegBa_adkRH_b.
Definition KS_adkRH : list nat := Eval vm_compute in (BG.kept_list 80 PadkRH.regs0 PadkRH.regs_out0).
Lemma KS_adkRH_ok : BG.kept_ok 80 PadkRH.regs0 PadkRH.regs_out0 KS_adkRH = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkRH_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 19) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 20) = Z_to_bv 64 1000000000 -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 23) = Z_to_bv 64 14757395259826634752 -> getr R (reg 25) = Z_to_bv 64 19342813113834067 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) + 64) + (36 * (V 40%nat))) -> getr R (reg 27) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 0 <= (V 40%nat) <= 3 ->
  4096 <= (V 50%nat) <= 140737488354816 -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 128) (V 42%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb4164 M) (st fx' R' 0xb417c M')
        /\ (forall x, In x KS_adkRH -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 7) = getr R (reg 7)
        /\ getr R' (reg 10) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAluw Instr.ALU_ADD (EVar 41) (ELit 0))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 40%nat)
        /\ bv_unsigned (getr R' (reg 28)) = (bv_unsigned (getr R (reg 28)))
        /\ bv_unsigned (getr R' (reg 30)) = (bv_unsigned (getr R (reg 30)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 41%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G22 G23 G25 G26 G27 pvzI6 K1 K2 pvzI7 pvzI8 K5 K6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV41l; move HV41l before pvzI3; pose proof (proj2 pvzI3) as HV41r; move HV41r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV42l; move HV42l before pvzI4; pose proof (proj2 pvzI4) as HV42r; move HV42r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkRH.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkRH.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkRH.kn0).
  { unfold know_ok, PadkRH.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkRH.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkRH.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkRH.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkRH.ps0) with 0xb417c in Hms. change (SR.ps_regs PadkRH.ps0) with (map (fun i => (i, nth i PadkRH.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkRH.ps0) with PadkRH.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRH.regs0 PadkRH.regs_out0 80 KS_adkRH KS_adkRH_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkRH.regs_out0 E' R' 7 Hregs) by (clear; lia). cbn [nth PadkRH.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadkRH.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRH.regs_out0]. apply (BG.edenot_kept 80 E E' _ Hag); vm_compute; reflexivity. }
  split. { rewrite (BG.out_reg PadkRH.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkRH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRH.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkRH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRH.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadkRH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkRH.regs_out0 E' R' 28 Hregs) by (clear; lia). cbn [nth PadkRH.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PadkRH.regs_out0 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkRH.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV42l HV42r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV41l HV41r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkRF := LibSegBa_adkRF_b.
Definition KS_adkRF_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRF.regs0 PadkRF.regs_out0).
Lemma KS_adkRF_0_ok : BG.kept_ok 80 PadkRF.regs0 PadkRF.regs_out0 KS_adkRF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkRF_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRF.regs0 PadkRF.regs_out1).
Lemma KS_adkRF_1_ok : BG.kept_ok 80 PadkRF.regs0 PadkRF.regs_out1 KS_adkRF_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkRF_2 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRF.regs0 PadkRF.regs_out2).
Lemma KS_adkRF_2_ok : BG.kept_ok 80 PadkRF.regs0 PadkRF.regs_out2 KS_adkRF_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkRF_3 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRF.regs0 PadkRF.regs_out3).
Lemma KS_adkRF_3_ok : BG.kept_ok 80 PadkRF.regs0 PadkRF.regs_out3 KS_adkRF_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkRF_4 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRF.regs0 PadkRF.regs_out4).
Lemma KS_adkRF_4_ok : BG.kept_ok 80 PadkRF.regs0 PadkRF.regs_out4 KS_adkRF_4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkRF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) -> getr R (reg 11) = Z_to_bv 64 (V 41%nat) -> getr R (reg 12) = Z_to_bv 64 (V 42%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 19) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 20) = Z_to_bv 64 1000000000 -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 23) = Z_to_bv 64 14757395259826634752 -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 19342813113834067 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) + 64) + (36 * (V 40%nat))) -> getr R (reg 27) = Z_to_bv 64 10 ->
  L5.u64_at RSEGS M ((V 2%nat) - 112) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 41%nat) -> 140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 ->
  L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 0 <= (V 40%nat) <= 3 -> 4096 <= (V 50%nat) <= 140737488354816 -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 41%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 128) (V 42%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb417c M) (st fx' R' 0xb4248 M')
        /\ (forall x, In x KS_adkRF_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EExt true 4 4 (EVar 42))
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551603
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 42)) (ELit 0)) (ELit 1))) <= 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 0 4 (EVar 42)) (ELit 0)) (ELit 1))) <= 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 41)) (ELit 0)) (ELit 1))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb417c M) (st fx' R' 0xb41c8 M')
        /\ (forall x, In x KS_adkRF_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 18) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28)
        /\ getr R' (reg 21) = Z_to_bv 64 0
        /\ getr R' (reg 28) = getr R (reg 28)
        /\ getr R' (reg 30) = getr R (reg 30)
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 42)) (ELit 0)) (ELit 1))) <= 0
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 0 4 (EVar 42)) (ELit 0)) (ELit 1))) <= 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 41)) (ELit 0)) (ELit 1))) <= 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb417c M) (st fx' R' 0xb41c8 M')
        /\ (forall x, In x KS_adkRF_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551607
        /\ getr R' (reg 18) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28)
        /\ getr R' (reg 21) = Z_to_bv 64 0
        /\ getr R' (reg 28) = getr R (reg 28)
        /\ getr R' (reg 30) = getr R (reg 30)
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 41)) (ELit 0)) (ELit 1))) <= 1
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 0 4 (EVar 42)) (ELit 0)) (ELit 1))) <= 0
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb417c M) (st fx' R' 0xb41c8 M')
        /\ (forall x, In x KS_adkRF_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 18) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28)
        /\ getr R' (reg 21) = Z_to_bv 64 0
        /\ getr R' (reg 28) = getr R (reg 28)
        /\ getr R' (reg 30) = getr R (reg 30)
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 41)) (ELit 0)) (ELit 1))) <= 0
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb417c M) (st fx' R' 0xb41c8 M')
        /\ (forall x, In x KS_adkRF_4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 18) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28)
        /\ getr R' (reg 21) = Z_to_bv 64 0
        /\ getr R' (reg 28) = getr R (reg 28)
        /\ getr R' (reg 30) = getr R (reg 30)
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G11 G12 G18 G19 G20 G22 G23 G24 G25 G26 G27 K0 K1 pvzI6 K3 K4 pvzI7 pvzI8 K7 K8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV41l; move HV41l before pvzI3; pose proof (proj2 pvzI3) as HV41r; move HV41r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV42l; move HV42l before pvzI4; pose proof (proj2 pvzI4) as HV42r; move HV42r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K2l; move K2l before pvzI6; pose proof (proj2 pvzI6) as K2r; move K2r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K5l; move K5l before pvzI7; pose proof (proj2 pvzI7) as K5r; move K5r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkRF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkRF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkRF.kn0).
  { unfold know_ok, PadkRF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K2l K2r; lia | clear - HV2l HV2r K2l K2r; lia | exactA K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K2l K2r; lia | clear - HV2l HV2r K2l K2r; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K2l K2r; lia | clear - HV2l HV2r K2l K2r; lia | clear - HV2l HV2r K2l K2r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K2l K2r; lia | clear - HV2l HV2r K2l K2r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K2l K2r) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K2l K2r; lia | clear - HV2l HV2r K2l K2r; lia | exactA K8]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkRF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkRF.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadkRF.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PadkRF.ps0) with 0xb4248 in Hms. change (SR.ps_regs PadkRF.ps0) with (map (fun i => (i, nth i PadkRF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkRF.ps0) with PadkRF.cells0 in Hcells. unfold PadkRF.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRF.regs0 PadkRF.regs_out0 80 KS_adkRF_0 KS_adkRF_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkRF.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out0]. apply (BG.edenot_kept 80 E E' _ Hag); vm_compute; reflexivity. }
    split. { rewrite (BG.out_reg PadkRF.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PadkRF.ps1) with 0xb41c8 in Hms. change (SR.ps_regs PadkRF.ps1) with (map (fun i => (i, nth i PadkRF.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkRF.ps1) with PadkRF.cells1 in Hcells. unfold PadkRF.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRF.regs0 PadkRF.regs_out1 80 KS_adkRF_1 KS_adkRF_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkRF.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRF.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRF.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRF.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRF.regs_out1 E' R' 28 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRF.regs_out1 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRF.regs_out1 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc PadkRF.ps2) with 0xb41c8 in Hms. change (SR.ps_regs PadkRF.ps2) with (map (fun i => (i, nth i PadkRF.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkRF.ps2) with PadkRF.cells2 in Hcells. unfold PadkRF.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRF.regs0 PadkRF.regs_out2 80 KS_adkRF_2 KS_adkRF_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkRF.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRF.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRF.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRF.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRF.regs_out2 E' R' 28 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out2]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRF.regs_out2 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out2]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRF.regs_out2 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out2]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. left.
    change (SR.ps_pc PadkRF.ps3) with 0xb41c8 in Hms. change (SR.ps_regs PadkRF.ps3) with (map (fun i => (i, nth i PadkRF.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkRF.ps3) with PadkRF.cells3 in Hcells. unfold PadkRF.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRF.regs0 PadkRF.regs_out3 80 KS_adkRF_3 KS_adkRF_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkRF.regs_out3 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRF.regs_out3 E' R' 18 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRF.regs_out3 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRF.regs_out3 E' R' 28 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out3]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRF.regs_out3 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out3]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRF.regs_out3 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out3]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. right.
    change (SR.ps_pc PadkRF.ps4) with 0xb41c8 in Hms. change (SR.ps_regs PadkRF.ps4) with (map (fun i => (i, nth i PadkRF.regs_out4 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkRF.ps4) with PadkRF.cells4 in Hcells. unfold PadkRF.cells4 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRF.regs0 PadkRF.regs_out4 80 KS_adkRF_4 KS_adkRF_4_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkRF.regs_out4 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRF.regs_out4 E' R' 18 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRF.regs_out4 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out4]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRF.regs_out4 E' R' 28 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out4]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRF.regs_out4 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out4]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRF.regs_out4 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkRF.regs_out4]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkL0 := LibSegBa_adkL0_b.
Definition KS_adkL0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkL0.regs0 PadkL0.regs_out0).
Lemma KS_adkL0_ok : BG.kept_ok 80 PadkL0.regs0 PadkL0.regs_out0 KS_adkL0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkL0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 ((V 2%nat) - 120) -> getr R (reg 18) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28) -> getr R (reg 19) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 20) = Z_to_bv 64 1000000000 -> getr R (reg 21) = Z_to_bv 64 (V 44%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 23) = Z_to_bv 64 14757395259826634752 -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 19342813113834067 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) + 64) + (36 * (V 40%nat))) -> getr R (reg 27) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 0 <= (V 40%nat) <= 3 ->
  4096 <= (V 50%nat) <= 140737488354816 -> 0 <= (V 44%nat) <= 999999999 -> L5.u32_at RSEGS M ((V 2%nat) - 120) (V 45%nat) -> 0 <= (V 45%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb41c8 M) (st fx' R' 0xb41c8 M')
        /\ (forall x, In x KS_adkL0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 116)
        /\ getr R' (reg 11) = Z_to_bv 64 ((4294967296 * (V 44%nat)) + (V 45%nat))
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EMd Instr.M_MUL (ELit 1000000000) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4294967296) (EVar 44)) (EVar 45)) (ELit 9)) (ELit 19342813113834067)) (ELit 11)))
        /\ getr R' (reg 21) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4294967296) (EVar 44)) (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1000000000)) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4294967296) (EVar 44)) (EVar 45)) (ELit 9)) (ELit 19342813113834067)) (ELit 11)))))
        /\ getr R' (reg 28) = getr R (reg 28)
        /\ bv_unsigned (getr R' (reg 29)) = (bv_unsigned (getr R (reg 29)))
        /\ bv_unsigned (getr R' (reg 31)) = (bv_unsigned (getr R (reg 31)))
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 120) ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI6 K1 K2 pvzI7 pvzI8 pvzI9 K6 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV44l; move HV44l before pvzI3; pose proof (proj2 pvzI3) as HV44r; move HV44r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV45l; move HV45l before pvzI4; pose proof (proj2 pvzI4) as HV45r; move HV45r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K5l; move K5l before pvzI9; pose proof (proj2 pvzI9) as K5r; move K5r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 44%nat => vz_44 | 45%nat => vz_45 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkL0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkL0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkL0.kn0).
  { unfold know_ok, PadkL0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r K7l K7r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkL0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkL0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkL0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkL0.ps0) with 0xb41c8 in Hms. change (SR.ps_regs PadkL0.ps0) with (map (fun i => (i, nth i PadkL0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkL0.ps0) with PadkL0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkL0.regs0 PadkL0.regs_out0 80 KS_adkL0 KS_adkL0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkL0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkL0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkL0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkL0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkL0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkL0.regs_out0]. apply (BG.edenot_kept 80 E E' _ Hag); vm_compute; reflexivity. }
  split. { rewrite (BG.out_reg PadkL0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkL0.regs_out0]. apply (BG.edenot_kept 80 E E' _ Hag); vm_compute; reflexivity. }
  split. { rewrite (BG.out_reg PadkL0.regs_out0 E' R' 28 Hregs) by (clear; lia). cbn [nth PadkL0.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadkL0.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth PadkL0.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PadkL0.regs_out0 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkL0.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkL1 := LibSegBa_adkL1_b.
Definition KS_adkL1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkL1.regs0 PadkL1.regs_out0).
Lemma KS_adkL1_ok : BG.kept_ok 80 PadkL1.regs0 PadkL1.regs_out0 KS_adkL1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkL1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 ((V 2%nat) - 116) -> getr R (reg 18) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28) -> getr R (reg 19) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 20) = Z_to_bv 64 1000000000 -> getr R (reg 21) = Z_to_bv 64 (V 44%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 23) = Z_to_bv 64 14757395259826634752 -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 19342813113834067 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) + 64) + (36 * (V 40%nat))) -> getr R (reg 27) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 0 <= (V 40%nat) <= 3 ->
  4096 <= (V 50%nat) <= 140737488354816 -> 0 <= (V 44%nat) <= 999999999 -> L5.u32_at RSEGS M ((V 2%nat) - 116) (V 45%nat) -> 0 <= (V 45%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 116) <= bv_unsigned a < ((V 2%nat) - 116) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 116) <= i < ((V 2%nat) - 116) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb41c8 M) (st fx' R' 0xb41c8 M')
        /\ (forall x, In x KS_adkL1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 11) = Z_to_bv 64 ((4294967296 * (V 44%nat)) + (V 45%nat))
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EMd Instr.M_MUL (ELit 1000000000) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4294967296) (EVar 44)) (EVar 45)) (ELit 9)) (ELit 19342813113834067)) (ELit 11)))
        /\ getr R' (reg 21) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4294967296) (EVar 44)) (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1000000000)) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4294967296) (EVar 44)) (EVar 45)) (ELit 9)) (ELit 19342813113834067)) (ELit 11)))))
        /\ getr R' (reg 28) = getr R (reg 28)
        /\ bv_unsigned (getr R' (reg 29)) = (bv_unsigned (getr R (reg 29)))
        /\ bv_unsigned (getr R' (reg 31)) = (bv_unsigned (getr R (reg 31)))
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 116) ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI6 K1 K2 pvzI7 pvzI8 pvzI9 K6 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV44l; move HV44l before pvzI3; pose proof (proj2 pvzI3) as HV44r; move HV44r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV45l; move HV45l before pvzI4; pose proof (proj2 pvzI4) as HV45r; move HV45r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K5l; move K5l before pvzI9; pose proof (proj2 pvzI9) as K5r; move K5r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 44%nat => vz_44 | 45%nat => vz_45 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkL1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkL1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkL1.kn0).
  { unfold know_ok, PadkL1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r K7l K7r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkL1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkL1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 116) <= bv_unsigned a < (vz_2 - 116) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkL1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkL1.ps0) with 0xb41c8 in Hms. change (SR.ps_regs PadkL1.ps0) with (map (fun i => (i, nth i PadkL1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkL1.ps0) with PadkL1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkL1.regs0 PadkL1.regs_out0 80 KS_adkL1 KS_adkL1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkL1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkL1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkL1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkL1.regs_out0]. apply (BG.edenot_kept 80 E E' _ Hag); vm_compute; reflexivity. }
  split. { rewrite (BG.out_reg PadkL1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkL1.regs_out0]. apply (BG.edenot_kept 80 E E' _ Hag); vm_compute; reflexivity. }
  split. { rewrite (BG.out_reg PadkL1.regs_out0 E' R' 28 Hregs) by (clear; lia). cbn [nth PadkL1.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadkL1.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth PadkL1.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PadkL1.regs_out0 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkL1.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkL2 := LibSegBa_adkL2_b.
Definition KS_adkL2 : list nat := Eval vm_compute in (BG.kept_list 80 PadkL2.regs0 PadkL2.regs_out0).
Lemma KS_adkL2_ok : BG.kept_ok 80 PadkL2.regs0 PadkL2.regs_out0 KS_adkL2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkL2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 ((V 2%nat) - 112) -> getr R (reg 18) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28) -> getr R (reg 19) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 20) = Z_to_bv 64 1000000000 -> getr R (reg 21) = Z_to_bv 64 (V 44%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 23) = Z_to_bv 64 14757395259826634752 -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 19342813113834067 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) + 64) + (36 * (V 40%nat))) -> getr R (reg 27) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 0 <= (V 40%nat) <= 3 ->
  4096 <= (V 50%nat) <= 140737488354816 -> 0 <= (V 44%nat) <= 999999999 -> L5.u32_at RSEGS M ((V 2%nat) - 112) (V 45%nat) -> 0 <= (V 45%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb41c8 M) (st fx' R' 0xb41c8 M')
        /\ (forall x, In x KS_adkL2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 108)
        /\ getr R' (reg 11) = Z_to_bv 64 ((4294967296 * (V 44%nat)) + (V 45%nat))
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EMd Instr.M_MUL (ELit 1000000000) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4294967296) (EVar 44)) (EVar 45)) (ELit 9)) (ELit 19342813113834067)) (ELit 11)))
        /\ getr R' (reg 21) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4294967296) (EVar 44)) (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1000000000)) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4294967296) (EVar 44)) (EVar 45)) (ELit 9)) (ELit 19342813113834067)) (ELit 11)))))
        /\ getr R' (reg 28) = getr R (reg 28)
        /\ bv_unsigned (getr R' (reg 29)) = (bv_unsigned (getr R (reg 29)))
        /\ bv_unsigned (getr R' (reg 31)) = (bv_unsigned (getr R (reg 31)))
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 112) ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI6 K1 K2 pvzI7 pvzI8 pvzI9 K6 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV44l; move HV44l before pvzI3; pose proof (proj2 pvzI3) as HV44r; move HV44r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV45l; move HV45l before pvzI4; pose proof (proj2 pvzI4) as HV45r; move HV45r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K5l; move K5l before pvzI9; pose proof (proj2 pvzI9) as K5r; move K5r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 44%nat => vz_44 | 45%nat => vz_45 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkL2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkL2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkL2.kn0).
  { unfold know_ok, PadkL2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r K7l K7r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkL2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkL2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 112) <= bv_unsigned a < (vz_2 - 112) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkL2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkL2.ps0) with 0xb41c8 in Hms. change (SR.ps_regs PadkL2.ps0) with (map (fun i => (i, nth i PadkL2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkL2.ps0) with PadkL2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkL2.regs0 PadkL2.regs_out0 80 KS_adkL2 KS_adkL2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkL2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkL2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkL2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkL2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkL2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkL2.regs_out0]. apply (BG.edenot_kept 80 E E' _ Hag); vm_compute; reflexivity. }
  split. { rewrite (BG.out_reg PadkL2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkL2.regs_out0]. apply (BG.edenot_kept 80 E E' _ Hag); vm_compute; reflexivity. }
  split. { rewrite (BG.out_reg PadkL2.regs_out0 E' R' 28 Hregs) by (clear; lia). cbn [nth PadkL2.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadkL2.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth PadkL2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PadkL2.regs_out0 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkL2.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkL3 := LibSegBa_adkL3_b.
Definition KS_adkL3 : list nat := Eval vm_compute in (BG.kept_list 80 PadkL3.regs0 PadkL3.regs_out0).
Lemma KS_adkL3_ok : BG.kept_ok 80 PadkL3.regs0 PadkL3.regs_out0 KS_adkL3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkL3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 ((V 2%nat) - 108) -> getr R (reg 18) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28) -> getr R (reg 19) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 20) = Z_to_bv 64 1000000000 -> getr R (reg 21) = Z_to_bv 64 (V 44%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 23) = Z_to_bv 64 14757395259826634752 -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 19342813113834067 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) + 64) + (36 * (V 40%nat))) -> getr R (reg 27) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 0 <= (V 40%nat) <= 3 ->
  4096 <= (V 50%nat) <= 140737488354816 -> 0 <= (V 44%nat) <= 999999999 -> L5.u32_at RSEGS M ((V 2%nat) - 108) (V 45%nat) -> 0 <= (V 45%nat) <= 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 108) <= bv_unsigned a < ((V 2%nat) - 108) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 108) <= i < ((V 2%nat) - 108) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb41c8 M) (st fx' R' 0xb41f4 M')
        /\ (forall x, In x KS_adkL3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 11) = Z_to_bv 64 ((4294967296 * (V 44%nat)) + (V 45%nat))
        /\ getr R' (reg 12) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EMd Instr.M_MUL (ELit 1000000000) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4294967296) (EVar 44)) (EVar 45)) (ELit 9)) (ELit 19342813113834067)) (ELit 11)))
        /\ getr R' (reg 21) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4294967296) (EVar 44)) (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1000000000)) (EAlu Instr.ALU_SRL (EMd Instr.M_MULHU (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4294967296) (EVar 44)) (EVar 45)) (ELit 9)) (ELit 19342813113834067)) (ELit 11)))))
        /\ getr R' (reg 28) = getr R (reg 28)
        /\ bv_unsigned (getr R' (reg 29)) = (bv_unsigned (getr R (reg 29)))
        /\ bv_unsigned (getr R' (reg 31)) = (bv_unsigned (getr R (reg 31)))
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 108) ((((((((4294967296 * (V 44%nat)) mod 2 ^ 64) + (V 45%nat)) mod 2 ^ 64) / 512) * 19342813113834067) / 2 ^ 64) / 2048)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI6 K1 K2 pvzI7 pvzI8 pvzI9 K6 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV44l; move HV44l before pvzI3; pose proof (proj2 pvzI3) as HV44r; move HV44r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV45l; move HV45l before pvzI4; pose proof (proj2 pvzI4) as HV45r; move HV45r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K4l; move K4l before pvzI8; pose proof (proj2 pvzI8) as K4r; move K4r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K5l; move K5l before pvzI9; pose proof (proj2 pvzI9) as K5r; move K5r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 44%nat => vz_44 | 45%nat => vz_45 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkL3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkL3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkL3.kn0).
  { unfold know_ok, PadkL3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r K7l K7r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkL3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkL3.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 108) <= bv_unsigned a < (vz_2 - 108) + 4) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadkL3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadkL3.ps0) with 0xb41f4 in Hms. change (SR.ps_regs PadkL3.ps0) with (map (fun i => (i, nth i PadkL3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadkL3.ps0) with PadkL3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkL3.regs0 PadkL3.regs_out0 80 KS_adkL3 KS_adkL3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadkL3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkL3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkL3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkL3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadkL3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkL3.regs_out0]. apply (BG.edenot_kept 80 E E' _ Hag); vm_compute; reflexivity. }
  split. { rewrite (BG.out_reg PadkL3.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PadkL3.regs_out0]. apply (BG.edenot_kept 80 E E' _ Hag); vm_compute; reflexivity. }
  split. { rewrite (BG.out_reg PadkL3.regs_out0 E' R' 28 Hregs) by (clear; lia). cbn [nth PadkL3.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PadkL3.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth PadkL3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  split. { rewrite (BG.out_reg PadkL3.regs_out0 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkL3.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkRM := LibSegBa_adkRM_b.
Definition KS_adkRM_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRM.regs0 PadkRM.regs_out0).
Lemma KS_adkRM_0_ok : BG.kept_ok 80 PadkRM.regs0 PadkRM.regs_out0 KS_adkRM_0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkRM_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 18) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28) -> getr R (reg 19) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 20) = Z_to_bv 64 1000000000 -> getr R (reg 21) = Z_to_bv 64 (V 48%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 23) = Z_to_bv 64 14757395259826634752 -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 19342813113834067 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) + 64) + (36 * (V 40%nat))) -> getr R (reg 27) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 0 <= (V 40%nat) <= 3 ->
  4096 <= (V 50%nat) <= 140737488354816 -> 0 <= (V 48%nat) <= 999999999 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb41f4 M) (st fx' R' 0x77c94 M')
        /\ (forall x, In x KS_adkRM_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 737796
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 12) = Z_to_bv 64 16)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI5 K1 K2 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV48l; move HV48l before pvzI3; pose proof (proj2 pvzI3) as HV48r; move HV48r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K5l; move K5l before pvzI8; pose proof (proj2 pvzI8) as K5r; move K5r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkRM.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkRM.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkRM.kn0).
  { unfold know_ok, PadkRM.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkRM.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkRM.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadkRM.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. 
    change (SR.ps_pc PadkRM.ps0) with 0x77c94 in Hms. change (SR.ps_regs PadkRM.ps0) with (map (fun i => (i, nth i PadkRM.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkRM.ps0) with PadkRM.cells0 in Hcells. unfold PadkRM.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRM.regs0 PadkRM.regs_out0 80 KS_adkRM_0 KS_adkRM_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkRM.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkRM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRM.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRM.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkRM.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PadkRM.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkRM.regs_out0]. first [reflexivity | wordP' ZA Hag].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module PadkRMr := LibSegBa_adkRMr_b.
Definition KS_adkRMr_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRMr.regs0 PadkRMr.regs_out0).
Lemma KS_adkRMr_0_ok : BG.kept_ok 80 PadkRMr.regs0 PadkRMr.regs_out0 KS_adkRMr_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkRMr_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRMr.regs0 PadkRMr.regs_out1).
Lemma KS_adkRMr_1_ok : BG.kept_ok 80 PadkRMr.regs0 PadkRMr.regs_out1 KS_adkRMr_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkRMr_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28) -> getr R (reg 19) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 20) = Z_to_bv 64 1000000000 -> getr R (reg 21) = Z_to_bv 64 (V 48%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 23) = Z_to_bv 64 14757395259826634752 -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 19342813113834067 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) + 64) + (36 * (V 40%nat))) -> getr R (reg 27) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 0 <= (V 40%nat) <= 3 ->
  4096 <= (V 50%nat) <= 140737488354816 -> 0 <= (V 48%nat) <= 999999999 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb4204 M) (st fx' R' 0xb4230 M')
        /\ (forall x, In x KS_adkRMr_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 28) = getr R (reg 28)
        /\ getr R' (reg 29) = getr R (reg 29)
        /\ (((V 48%nat) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb4204 M) (st fx' R' 0xb420c M')
        /\ (forall x, In x KS_adkRMr_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 64)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 28) = getr R (reg 28)
        /\ getr R' (reg 29) = getr R (reg 29)
        /\ 1 <= (((V 48%nat) - 0) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI5 K1 K2 pvzI6 pvzI7 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV48l; move HV48l before pvzI3; pose proof (proj2 pvzI3) as HV48r; move HV48r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K5l; move K5l before pvzI8; pose proof (proj2 pvzI8) as K5r; move K5r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkRMr.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkRMr.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkRMr.kn0).
  { unfold know_ok, PadkRMr.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkRMr.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkRMr.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadkRMr.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PadkRMr.ps0) with 0xb4230 in Hms. change (SR.ps_regs PadkRMr.ps0) with (map (fun i => (i, nth i PadkRMr.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkRMr.ps0) with PadkRMr.cells0 in Hcells. unfold PadkRMr.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRMr.regs0 PadkRMr.regs_out0 80 KS_adkRMr_0 KS_adkRMr_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkRMr.regs_out0 E' R' 28 Hregs) by (clear; lia). cbn [nth PadkRMr.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRMr.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth PadkRMr.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right.
    change (SR.ps_pc PadkRMr.ps1) with 0xb420c in Hms. change (SR.ps_regs PadkRMr.ps1) with (map (fun i => (i, nth i PadkRMr.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkRMr.ps1) with PadkRMr.cells1 in Hcells. unfold PadkRMr.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRMr.regs0 PadkRMr.regs_out1 80 KS_adkRMr_1 KS_adkRMr_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkRMr.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRMr.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRMr.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PadkRMr.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRMr.regs_out1 E' R' 28 Hregs) by (clear; lia). cbn [nth PadkRMr.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRMr.regs_out1 E' R' 29 Hregs) by (clear; lia). cbn [nth PadkRMr.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkRT := LibSegBa_adkRT_b.
Definition KS_adkRT_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRT.regs0 PadkRT.regs_out0).
Lemma KS_adkRT_0_ok : BG.kept_ok 80 PadkRT.regs0 PadkRT.regs_out0 KS_adkRT_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkRT_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRT.regs0 PadkRT.regs_out1).
Lemma KS_adkRT_1_ok : BG.kept_ok 80 PadkRT.regs0 PadkRT.regs_out1 KS_adkRT_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkRT_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28) -> getr R (reg 19) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 20) = Z_to_bv 64 1000000000 -> getr R (reg 21) = Z_to_bv 64 (V 48%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 23) = Z_to_bv 64 14757395259826634752 -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 19342813113834067 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) + 64) + (36 * (V 40%nat))) -> getr R (reg 27) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 0 <= (V 40%nat) <= 3 ->
  4096 <= (V 50%nat) <= 140737488354816 -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb4230 M) (st fx' R' 0xb4268 M')
        /\ (forall x, In x KS_adkRT_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) - 1)
        /\ getr R' (reg 14) = getr R (reg 14)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 19) = Z_to_bv 64 (((-1) * (V 40%nat)) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28)
        /\ getr R' (reg 28) = getr R (reg 28)
        /\ getr R' (reg 30) = getr R (reg 30)
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ (((V 40%nat) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb4230 M) (st fx' R' 0xb4164 M')
        /\ (forall x, In x KS_adkRT_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) - 1)
        /\ getr R' (reg 14) = getr R (reg 14)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 50%nat) + 32)
        /\ getr R' (reg 19) = Z_to_bv 64 (((-1) * (V 40%nat)) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28)
        /\ getr R' (reg 28) = getr R (reg 28)
        /\ getr R' (reg 30) = getr R (reg 30)
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ 1 <= (((V 40%nat) - 0) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI5 K1 K2 pvzI6 pvzI7 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV48l; move HV48l before pvzI3; pose proof (proj2 pvzI3) as HV48r; move HV48r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkRT.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkRT.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkRT.kn0).
  { unfold know_ok, PadkRT.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV50l HV50r K4l K4r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkRT.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkRT.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadkRT.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PadkRT.ps0) with 0xb4268 in Hms. change (SR.ps_regs PadkRT.ps0) with (map (fun i => (i, nth i PadkRT.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkRT.ps0) with PadkRT.cells0 in Hcells. unfold PadkRT.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRT.regs0 PadkRT.regs_out0 80 KS_adkRT_0 KS_adkRT_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkRT.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRT.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT.regs_out0 E' R' 28 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRT.regs_out0 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRT.regs_out0 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right.
    change (SR.ps_pc PadkRT.ps1) with 0xb4164 in Hms. change (SR.ps_regs PadkRT.ps1) with (map (fun i => (i, nth i PadkRT.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkRT.ps1) with PadkRT.cells1 in Hcells. unfold PadkRT.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRT.regs0 PadkRT.regs_out1 80 KS_adkRT_1 KS_adkRT_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkRT.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRT.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT.regs_out1 E' R' 28 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRT.regs_out1 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRT.regs_out1 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkRT.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkRT0 := LibSegBa_adkRT0_b.
Definition KS_adkRT0_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRT0.regs0 PadkRT0.regs_out0).
Lemma KS_adkRT0_0_ok : BG.kept_ok 80 PadkRT0.regs0 PadkRT0.regs_out0 KS_adkRT0_0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkRT0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 12) = Z_to_bv 64 (V 42%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 19) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 20) = Z_to_bv 64 1000000000 -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 23) = Z_to_bv 64 14757395259826634752 -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 19342813113834067 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) + 64) + (36 * (V 40%nat))) -> getr R (reg 27) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 0 <= (V 40%nat) <= 3 ->
  4096 <= (V 50%nat) <= 140737488354816 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb4248 M) (st fx' R' 0x77c94 M')
        /\ (forall x, In x KS_adkRT0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 737880
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 12) = Z_to_bv 64 16)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G12 G18 G19 G20 G22 G23 G24 G25 G26 G27 pvzI5 K1 K2 pvzI6 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV42l; move HV42l before pvzI3; pose proof (proj2 pvzI3) as HV42r; move HV42r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 42%nat => vz_42 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkRT0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkRT0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkRT0.kn0).
  { unfold know_ok, PadkRT0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkRT0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkRT0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadkRT0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. 
    change (SR.ps_pc PadkRT0.ps0) with 0x77c94 in Hms. change (SR.ps_regs PadkRT0.ps0) with (map (fun i => (i, nth i PadkRT0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkRT0.ps0) with PadkRT0.cells0 in Hcells. unfold PadkRT0.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRT0.regs0 PadkRT0.regs_out0 80 KS_adkRT0_0 KS_adkRT0_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkRT0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PadkRT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadkRT0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    rewrite (BG.out_reg PadkRT0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadkRT0.regs_out0]. first [reflexivity | wordP' ZA Hag].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module PadkRT0r := LibSegBa_adkRT0r_b.
Definition KS_adkRT0r_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRT0r.regs0 PadkRT0r.regs_out0).
Lemma KS_adkRT0r_0_ok : BG.kept_ok 80 PadkRT0r.regs0 PadkRT0r.regs_out0 KS_adkRT0r_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkRT0r_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkRT0r.regs0 PadkRT0r.regs_out1).
Lemma KS_adkRT0r_1_ok : BG.kept_ok 80 PadkRT0r.regs0 PadkRT0r.regs_out1 KS_adkRT0r_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkRT0r_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 19) = Z_to_bv 64 (3 - (V 40%nat)) -> getr R (reg 20) = Z_to_bv 64 1000000000 -> getr R (reg 22) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 23) = Z_to_bv 64 14757395259826634752 -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 19342813113834067 -> getr R (reg 26) = Z_to_bv 64 (((V 50%nat) + 64) + (36 * (V 40%nat))) -> getr R (reg 27) = Z_to_bv 64 10 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 0 <= (V 40%nat) <= 3 ->
  4096 <= (V 50%nat) <= 140737488354816 -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb4258 M) (st fx' R' 0xb4268 M')
        /\ (forall x, In x KS_adkRT0r_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) - 1)
        /\ getr R' (reg 14) = getr R (reg 14)
        /\ getr R' (reg 19) = Z_to_bv 64 (((-1) * (V 40%nat)) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28)
        /\ getr R' (reg 28) = getr R (reg 28)
        /\ getr R' (reg 29) = getr R (reg 29)
        /\ getr R' (reg 30) = getr R (reg 30)
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ (((V 40%nat) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb4258 M) (st fx' R' 0xb4164 M')
        /\ (forall x, In x KS_adkRT0r_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) - 1)
        /\ getr R' (reg 14) = getr R (reg 14)
        /\ getr R' (reg 19) = Z_to_bv 64 (((-1) * (V 40%nat)) + 4)
        /\ getr R' (reg 26) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28)
        /\ getr R' (reg 28) = getr R (reg 28)
        /\ getr R' (reg 29) = getr R (reg 29)
        /\ getr R' (reg 30) = getr R (reg 30)
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ 1 <= (((V 40%nat) - 0) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G8 G9 G18 G19 G20 G22 G23 G24 G25 G26 G27 pvzI4 K1 K2 pvzI5 pvzI6 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV40l; move HV40l before pvzI2; pose proof (proj2 pvzI2) as HV40r; move HV40r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV50l; move HV50l before pvzI3; pose proof (proj2 pvzI3) as HV50r; move HV50r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K4l; move K4l before pvzI6; pose proof (proj2 pvzI6) as K4r; move K4r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 40%nat => Z_to_bv 64 vz_40 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 40%nat => vz_40 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PadkRT0r.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadkRT0r.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadkRT0r.kn0).
  { unfold know_ok, PadkRT0r.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV50l HV50r K4l K4r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadkRT0r.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadkRT0r.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadkRT0r.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PadkRT0r.ps0) with 0xb4268 in Hms. change (SR.ps_regs PadkRT0r.ps0) with (map (fun i => (i, nth i PadkRT0r.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkRT0r.ps0) with PadkRT0r.cells0 in Hcells. unfold PadkRT0r.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRT0r.regs0 PadkRT0r.regs_out0 80 KS_adkRT0r_0 KS_adkRT0r_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out0 E' R' 28 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out0 E' R' 29 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out0 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out0 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right.
    change (SR.ps_pc PadkRT0r.ps1) with 0xb4164 in Hms. change (SR.ps_regs PadkRT0r.ps1) with (map (fun i => (i, nth i PadkRT0r.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadkRT0r.ps1) with PadkRT0r.cells1 in Hcells. unfold PadkRT0r.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadkRT0r.regs0 PadkRT0r.regs_out1 80 KS_adkRT0r_1 KS_adkRT0r_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out1 E' R' 28 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out1 E' R' 29 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out1 E' R' 30 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadkRT0r.regs_out1 E' R' 31 Hregs) by (clear; lia). cbn [nth PadkRT0r.regs_out1]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

End PNADP3.
