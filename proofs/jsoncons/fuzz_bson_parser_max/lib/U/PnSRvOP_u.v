(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BigLinkZA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore
     BigLinkBase. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import BigLinkGlue_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import L5Kn_u L5KnA_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_vlO0_u LibSegBs_vlO1_u LibSegBs_vlO2_u LibSegBs_vlO3_u LibSegBs_vlO4_u LibSegBs_vlOH_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRVOP.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).

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
Definition u16_at (M : word -> option byte) (a v : Z) : Prop := rdn RSEGS M (Z_to_bv 64 a) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 v)).
Lemma kentry_KWord2a E M b off e a v :
  bv_unsigned (edenot E b) = a -> bv_unsigned (edenot E e) = v ->
  0 <= a + off -> a + off + 2 <= 2 ^ 64 ->
  u16_at M (a + off) v -> kentry_ok RSEGS E M (KWord (SA b off) 2 e).
Proof.
  intros Ha Hv H1 H2 Hu. cbn [kentry_ok]. split. lia. split.
  - unfold flat. rewrite L5K.estart_e, Ha. lia.
  - rewrite L5K.adenot_e, Ha. rewrite (BG.word_of_unsigned _ _ Hv). exact Hu.
Qed.
Lemma rd2_of_KWord2x E M b off j a v a' : kentry_ok RSEGS E M (KWord (SA b off) 2 (EExt true 0 2 (EVar j))) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E (EVar j)) = v -> 0 <= v < 2 ^ 16 -> a' = a + off ->
  rdn RSEGS M (Z_to_bv 64 a') 2 = Some (word_to_le_bytes 2 (v_lh (Z_to_bv 64 v))).
Proof.
  intros K Ha Hv Hr ->. cbn [kentry_ok] in K. destruct K as (_ & _ & Rd). rewrite L5K.adenot_e, Ha in Rd. rewrite Rd. do 2 f_equal.
  cbn [edenot] in Hv |- *. unfold AX2.ext_val, AX2.ext_Z, v_lh. rewrite Hv. rewrite L5.unsigned_lit by lia.
  change (8 * Z.of_nat 0) with 0. change (2 ^ 0) with 1. rewrite Z.div_1_r. change (8 * Z.of_nat 2) with 16. change (8 * N.of_nat 2)%N with 16%N.
  rewrite (Z.mod_small v (2 ^ 16)) by lia. reflexivity.
Qed.
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
          | |- u16_at _ ?a _ => lazymatch type of H with u16_at _ ?b _ => replace a with b by (clear; lia) end
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
Module PvlO0 := LibSegBs_vlO0_u.
Definition KS_vlO0 : list nat := Eval vm_compute in (BG.kept_list 72 PvlO0.regs0 PvlO0.regs_out0).
Lemma KS_vlO0_ok : BG.kept_ok 72 PvlO0.regs0 PvlO0.regs_out0 KS_vlO0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlO0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x379a4 M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_vlO0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 227764
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 12) = Z_to_bv 64 12).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G18 pvzI5 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlO0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlO0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlO0.kn0).
  { unfold know_ok, PvlO0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlO0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlO0.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlO0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlO0.ps0) with 0x370d0 in Hms. change (SR.ps_regs PvlO0.ps0) with (map (fun i => (i, nth i PvlO0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlO0.ps0) with PvlO0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlO0.regs0 PvlO0.regs_out0 72 KS_vlO0 KS_vlO0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlO0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlO0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlO0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlO0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlO0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlO0.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlO1 := LibSegBs_vlO1_u.
Definition KS_vlO1_0 : list nat := Eval vm_compute in (BG.kept_list 72 PvlO1.regs0 PvlO1.regs_out0).
Lemma KS_vlO1_0_ok : BG.kept_ok 72 PvlO1.regs0 PvlO1.regs_out0 KS_vlO1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_vlO1_1 : list nat := Eval vm_compute in (BG.kept_list 72 PvlO1.regs0 PvlO1.regs_out1).
Lemma KS_vlO1_1_ok : BG.kept_ok 72 PvlO1.regs0 PvlO1.regs_out1 KS_vlO1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlO1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> 140735332483248 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 176)) -> L5.u64_at RSEGS M ((V 33%nat) + 400) (V 51%nat) -> 4136 <= (V 51%nat) <= 140737488355328 ->
  aligned (V 51%nat) 8 -> (((V 2%nat) - 176) + 176 <= ((V 51%nat) - 40) \/ ((V 51%nat) - 40) + 40 <= ((V 2%nat) - 176)) -> (((V 51%nat) - 40) + 40 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 51%nat) - 40)) ->
  (((V 51%nat) - 40) + 40 <= (V 36%nat) \/ (V 36%nat) + 16 <= ((V 51%nat) - 40)) -> (((V 51%nat) - 40) + 40 <= 65536 \/ 65536 + 897024 <= ((V 51%nat) - 40)) -> L5.u64_at RSEGS M ((V 51%nat) - 24) (V 52%nat) -> L5.writable RSEGS M ((V 51%nat) - 24) 8 ->
  0 <= (V 50%nat) <= 12 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 51%nat) - 24) <= bv_unsigned a < ((V 51%nat) - 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 51%nat) - 24) <= i < ((V 51%nat) - 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x379b4 M) (st fx' R' 0x37d98 M')
        /\ (forall x, In x KS_vlO1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 51%nat)
        /\ bv_unsigned (getr R' (reg 12)) = (((V 50%nat) + (V 52%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 12
        /\ 1 <= (((V 50%nat) - 12) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x379b4 M) (st fx' R' 0x379e4 M')
        /\ (forall x, In x KS_vlO1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 51%nat)
        /\ bv_unsigned (getr R' (reg 12)) = (((V 50%nat) + (V 52%nat)) mod 2 ^ 64)
        /\ getr R' (reg 13) = Z_to_bv 64 12
        /\ (((V 50%nat) - 12) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 24) (((V 50%nat) + (V 52%nat)) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G10 G18 pvzI8 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 K10 K11 K12 K13 K14 K15 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV51l; move HV51l before pvzI6; pose proof (proj2 pvzI6) as HV51r; move HV51r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV52l; move HV52l before pvzI7; pose proof (proj2 pvzI7) as HV52r; move HV52r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K16l; move K16l before pvzI11; pose proof (proj2 pvzI11) as K16r; move K16r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PvlO1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlO1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlO1.kn0).
  { unfold know_ok, PvlO1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9; lia | clear - HV2l HV2r K0l K0r K5 K9; lia | clear - HV2l HV2r K0l K0r K5 K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear - HV33l HV33r K3l K3r K5 K10; lia | clear - HV33l HV33r K3l K3r K5 K10; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlO1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlO1.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_51 - 24) <= bv_unsigned a < (vz_51 - 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvlO1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PvlO1.ps0) with 0x37d98 in Hms. change (SR.ps_regs PvlO1.ps0) with (map (fun i => (i, nth i PvlO1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlO1.ps0) with PvlO1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlO1.regs0 PvlO1.regs_out0 72 KS_vlO1_0 KS_vlO1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlO1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlO1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlO1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlO1.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PvlO1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlO1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
  - right.
    change (SR.ps_pc PvlO1.ps1) with 0x379e4 in Hms. change (SR.ps_regs PvlO1.ps1) with (map (fun i => (i, nth i PvlO1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PvlO1.ps1) with PvlO1.cells1 in Hcells. unfold PvlO1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlO1.regs0 PvlO1.regs_out1 72 KS_vlO1_1 KS_vlO1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PvlO1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlO1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PvlO1.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlO1.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PvlO1.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlO1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K7l K7r K9 K10 K11 K12 K13) | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlO2 := LibSegBs_vlO2_u.
Definition KS_vlO2 : list nat := Eval vm_compute in (BG.kept_list 72 PvlO2.regs0 PvlO2.regs_out0).
Lemma KS_vlO2_ok : BG.kept_ok 72 PvlO2.regs0 PvlO2.regs_out0 KS_vlO2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlO2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.u8_at RSEGS M ((V 2%nat) - 80) (V 60%nat) ->
  L5.u8_at RSEGS M ((V 2%nat) - 79) (V 61%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 78) (V 62%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 77) (V 63%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 76) (V 64%nat) ->
  L5.u8_at RSEGS M ((V 2%nat) - 75) (V 65%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 74) (V 66%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 73) (V 67%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 72) (V 68%nat) ->
  L5.u8_at RSEGS M ((V 2%nat) - 71) (V 69%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 70) (V 70%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 69) (V 71%nat) -> 0 <= (V 60%nat) <= 255 ->
  0 <= (V 61%nat) <= 255 -> 0 <= (V 62%nat) <= 255 -> 0 <= (V 63%nat) <= 255 -> 0 <= (V 64%nat) <= 255 ->
  0 <= (V 65%nat) <= 255 -> 0 <= (V 66%nat) <= 255 -> 0 <= (V 67%nat) <= 255 -> 0 <= (V 68%nat) <= 255 ->
  0 <= (V 69%nat) <= 255 -> 0 <= (V 70%nat) <= 255 -> 0 <= (V 71%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 96) <= bv_unsigned a < ((V 2%nat) - 96) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 96) <= i < ((V 2%nat) - 96) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x379e4 M) (st fx' R' 0x59000 M')
        /\ (forall x, In x KS_vlO2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 227964
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 368)
        /\ getr R' (reg 11) = Z_to_bv 64 24
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((65536 * (V 66%nat)) + (16777216 * (V 67%nat)))
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 60%nat) + ((256 * (V 61%nat)) + ((65536 * (V 62%nat)) + (16777216 * (V 63%nat)))))
        /\ getr R' (reg 15) = Z_to_bv 64 ((65536 * (V 62%nat)) + (16777216 * (V 63%nat)))
        /\ getr R' (reg 16) = Z_to_bv 64 (65536 * (V 66%nat))
        /\ getr R' (reg 17) = Z_to_bv 64 (16777216 * (V 67%nat))
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 88) ((V 68%nat) + ((256 * (V 69%nat)) + ((65536 * (V 70%nat)) + (16777216 * (V 71%nat)))))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 60%nat) + ((256 * (V 61%nat)) + ((65536 * (V 62%nat)) + ((16777216 * (V 63%nat)) + ((4294967296 * (V 64%nat)) + ((1099511627776 * (V 65%nat)) + ((281474976710656 * (V 66%nat)) + (72057594037927936 * (V 67%nat)))))))))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G8 G9 G18 pvzI17 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 pvzI18 pvzI19 pvzI20 pvzI21 pvzI22 pvzI23 pvzI24 pvzI25 pvzI26 pvzI27 pvzI28 pvzI29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV60l; move HV60l before pvzI5; pose proof (proj2 pvzI5) as HV60r; move HV60r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV61l; move HV61l before pvzI6; pose proof (proj2 pvzI6) as HV61r; move HV61r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV62l; move HV62l before pvzI7; pose proof (proj2 pvzI7) as HV62r; move HV62r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV63l; move HV63l before pvzI8; pose proof (proj2 pvzI8) as HV63r; move HV63r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV69l; move HV69l before pvzI14; pose proof (proj2 pvzI14) as HV69r; move HV69r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV70l; move HV70l before pvzI15; pose proof (proj2 pvzI15) as HV70r; move HV70r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV71l; move HV71l before pvzI16; pose proof (proj2 pvzI16) as HV71r; move HV71r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K0l; move K0l before pvzI17; pose proof (proj2 pvzI17) as K0r; move K0r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K15l; move K15l before pvzI18; pose proof (proj2 pvzI18) as K15r; move K15r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K16l; move K16l before pvzI19; pose proof (proj2 pvzI19) as K16r; move K16r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K17l; move K17l before pvzI20; pose proof (proj2 pvzI20) as K17r; move K17r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K18l; move K18l before pvzI21; pose proof (proj2 pvzI21) as K18r; move K18r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K19l; move K19l before pvzI22; pose proof (proj2 pvzI22) as K19r; move K19r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K20l; move K20l before pvzI23; pose proof (proj2 pvzI23) as K20r; move K20r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K21l; move K21l before pvzI24; pose proof (proj2 pvzI24) as K21r; move K21r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K22l; move K22l before pvzI25; pose proof (proj2 pvzI25) as K22r; move K22r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K23l; move K23l before pvzI26; pose proof (proj2 pvzI26) as K23r; move K23r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K24l; move K24l before pvzI27; pose proof (proj2 pvzI27) as K24r; move K24r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K25l; move K25l before pvzI28; pose proof (proj2 pvzI28) as K25r; move K25r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K26l; move K26l before pvzI29; pose proof (proj2 pvzI29) as K26r; move K26r before pvzI29; clear pvzI29.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 72%nat. }
  assert (HR: regs_ok E PvlO2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlO2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlO2.kn0).
  { unfold know_ok, PvlO2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV60l HV60r K15l K15r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV60l HV60r K15l K15r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV61l HV61r K16l K16r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV61l HV61r K16l K16r) | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV62l HV62r K17l K17r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV62l HV62r K17l K17r) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV63l HV63r K18l K18r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV63l HV63r K18l K18r) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV64l HV64r K19l K19r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV64l HV64r K19l K19r) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV65l HV65r K20l K20r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV65l HV65r K20l K20r) | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV66l HV66r K21l K21r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV66l HV66r K21l K21r) | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV67l HV67r K22l K22r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV67l HV67r K22l K22r) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV68l HV68r K23l K23r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV68l HV68r K23l K23r) | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV69l HV69r K24l K24r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV69l HV69r K24l K24r) | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV70l HV70r K25l K25r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV70l HV70r K25l K25r) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV71l HV71r K26l K26r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | byte_tac ltac:(clear - HV71l HV71r K26l K26r) | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV63l HV63r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlO2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlO2.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 96) <= bv_unsigned a < (vz_2 - 96) + 12) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvlO2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlO2.ps0) with 0x59000 in Hms. change (SR.ps_regs PvlO2.ps0) with (map (fun i => (i, nth i PvlO2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlO2.ps0) with PvlO2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlO2.regs0 PvlO2.regs_out0 72 KS_vlO2 KS_vlO2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlO2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvlO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvlO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO2.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PvlO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO2.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PvlO2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV68l HV68r K23l K23r HV69l HV69r K24l K24r HV70l HV70r K25l K25r HV71l HV71r K26l K26r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear - HV60l HV60r K15l K15r HV61l HV61r K16l K16r HV62l HV62r K17l K17r HV63l HV63r K18l K18r HV64l HV64r K19l K19r HV65l HV65r K20l K20r HV66l HV66r K21l K21r HV67l HV67r K22l K22r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlO3 := LibSegBs_vlO3_u.
Definition KS_vlO3 : list nat := Eval vm_compute in (BG.kept_list 72 PvlO3.regs0 PvlO3.regs_out0).
Lemma KS_vlO3_ok : BG.kept_ok 72 PvlO3.regs0 PvlO3.regs_out0 KS_vlO3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlO3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> 140735332483248 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 176)) -> L5.u8_at RSEGS M ((V 33%nat) + 368) (V 56%nat) -> 0 <= (V 56%nat) <= 255 ->
  Z.testbit (V 56%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 384) (V 57%nat) -> 4096 <= (V 57%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x37a7c M) (st fx' R' 0x39bf8 M')
        /\ (forall x, In x KS_vlO3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 228448
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 57%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 pvzI7 K1 K2 pvzI8 K4 K5 K6 pvzI9 K8 K9 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV56l; move HV56l before pvzI5; pose proof (proj2 pvzI5) as HV56r; move HV56r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV57l; move HV57l before pvzI6; pose proof (proj2 pvzI6) as HV57r; move HV57r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K10l; move K10l before pvzI10; pose proof (proj2 pvzI10) as K10r; move K10r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PvlO3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlO3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlO3.kn0).
  { unfold know_ok, PvlO3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear - HV56l HV56r K7l K7r K8) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | byte_tac ltac:(clear - HV56l HV56r K7l K7r K8) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV56l HV56r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_true vz_56 ltac:(clear - HV56l HV56r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear - HV57l HV57r K10l K10r) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlO3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlO3.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlO3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlO3.ps0) with 0x39bf8 in Hms. change (SR.ps_regs PvlO3.ps0) with (map (fun i => (i, nth i PvlO3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlO3.ps0) with PvlO3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlO3.regs0 PvlO3.regs_out0 72 KS_vlO3 KS_vlO3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlO3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlO3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlO3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlO3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlO3.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlO4 := LibSegBs_vlO4_u.
Definition KS_vlO4 : list nat := Eval vm_compute in (BG.kept_list 72 PvlO4.regs0 PvlO4.regs_out0).
Lemma KS_vlO4_ok : BG.kept_ok 72 PvlO4.regs0 PvlO4.regs_out0 KS_vlO4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlO4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> 140735332483248 <= (V 33%nat) <= 140737488354912 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 33%nat) \/ (V 33%nat) + 416 <= ((V 2%nat) - 176)) -> L5.u8_at RSEGS M ((V 33%nat) + 368) (V 56%nat) -> 0 <= (V 56%nat) <= 255 ->
  Z.testbit (V 56%nat) 0 = true -> L5.u64_at RSEGS M ((V 33%nat) + 384) (V 57%nat) -> 4096 <= (V 57%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 33%nat) + 376) (V 58%nat) ->
  140735332483248 <= (V 34%nat) <= 140737488355320 -> aligned (V 34%nat) 8 -> (((V 2%nat) - 176) + 176 <= (V 34%nat) \/ (V 34%nat) + 8 <= ((V 2%nat) - 176)) -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M (V 34%nat) 726280 -> ((V 33%nat) + 416 <= (V 34%nat) \/ (V 34%nat) + 8 <= (V 33%nat)) -> L5.u8_at RSEGS M ((V 33%nat) + 10) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x37c60 M) (st fx' R' 0x37d74 M')
        /\ (forall x, In x KS_vlO4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 228704
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 19
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 216348
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 58%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 57%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G18 pvzI8 K1 K2 pvzI9 K4 K5 K6 pvzI10 K8 K9 pvzI11 K11 pvzI12 K13 K14 K15 K16 K17 K18.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV56l; move HV56l before pvzI5; pose proof (proj2 pvzI5) as HV56r; move HV56r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV57l; move HV57l before pvzI6; pose proof (proj2 pvzI6) as HV57r; move HV57r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV58l; move HV58l before pvzI7; pose proof (proj2 pvzI7) as HV58r; move HV58r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K10l; move K10l before pvzI11; pose proof (proj2 pvzI11) as K10r; move K10r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K12l; move K12l before pvzI12; pose proof (proj2 pvzI12) as K12r; move K12r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 59%nat. }
  assert (HR: regs_ok E PvlO4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlO4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlO4.kn0).
  { unfold know_ok, PvlO4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | clear - HV2l HV2r K0l K0r K5 K14; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K17) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K17) | evalEk ZA ltac:(clear - HV56l HV56r K7l K7r K8) | clear - HV33l HV33r K3l K3r K5 K17; lia | clear - HV33l HV33r K3l K3r K5 K17; lia | byte_tac ltac:(clear - HV56l HV56r K7l K7r K8) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K7l K7r K8) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV56l HV56r K7l K7r K8) | clear; lia | rewrite (L5K.land1_bit0_true vz_56 ltac:(clear - HV56l HV56r K7l K7r K8; lia) K8); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K17) | evalEk ZA ltac:(clear - HV57l HV57r K10l K10r) | clear - HV33l HV33r K3l K3r K5 K17; lia | clear - HV33l HV33r K3l K3r K5 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K17) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV33l HV33r K3l K3r K5 K17; lia | clear - HV33l HV33r K3l K3r K5 K17; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K12l K12r K14 K17; lia | clear - HV34l HV34r K12l K12r K14 K17; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K17) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K17; lia | clear - HV33l HV33r K3l K3r K5 K17; lia | byte_tac ltac:(clear) | exactA K18]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlO4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlO4.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 64) <= bv_unsigned a < (vz_2 - 64) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvlO4.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K14 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlO4.ps0) with 0x37d74 in Hms. change (SR.ps_regs PvlO4.ps0) with (map (fun i => (i, nth i PvlO4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlO4.ps0) with PvlO4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlO4.regs0 PvlO4.regs_out0 72 KS_vlO4 KS_vlO4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlO4.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvlO4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlO4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlO4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO4.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlO4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO4.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlO4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO4.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvlO4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlO4.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvlO4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear - HV58l HV58r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K14) | evalEk' ZA Hag ltac:(clear - HV57l HV57r K10l K10r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

Module PvlOH := LibSegBs_vlOH_u.
Definition KS_vlOH : list nat := Eval vm_compute in (BG.kept_list 84 PvlOH.regs0 PvlOH.regs_out0).
Lemma KS_vlOH_ok : BG.kept_ok 84 PvlOH.regs0 PvlOH.regs_out0 KS_vlOH = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlOH_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 61%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 -> 0 <= (V 63%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 78%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 -> 0 <= (V 80%nat) < 2 ^ 64 -> 0 <= (V 81%nat) < 2 ^ 64 -> 0 <= (V 82%nat) < 2 ^ 64 -> 0 <= (V 83%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 228448 -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 11) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.u8_at RSEGS M ((V 2%nat) - 96) (V 60%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 95) (V 61%nat) ->
  L5.u8_at RSEGS M ((V 2%nat) - 94) (V 62%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 93) (V 63%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 92) (V 64%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 91) (V 65%nat) ->
  L5.u8_at RSEGS M ((V 2%nat) - 90) (V 66%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 89) (V 67%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 88) (V 68%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 87) (V 69%nat) ->
  L5.u8_at RSEGS M ((V 2%nat) - 86) (V 70%nat) -> L5.u8_at RSEGS M ((V 2%nat) - 85) (V 71%nat) -> 0 <= (V 60%nat) <= 255 -> 0 <= (V 61%nat) <= 255 ->
  0 <= (V 62%nat) <= 255 -> 0 <= (V 63%nat) <= 255 -> 0 <= (V 64%nat) <= 255 -> 0 <= (V 65%nat) <= 255 ->
  0 <= (V 66%nat) <= 255 -> 0 <= (V 67%nat) <= 255 -> 0 <= (V 68%nat) <= 255 -> 0 <= (V 69%nat) <= 255 ->
  0 <= (V 70%nat) <= 255 -> 0 <= (V 71%nat) <= 255 -> 4096 <= (V 57%nat) <= 140737488355328 -> aligned (V 57%nat) 2 ->
  L5.writable RSEGS M (V 57%nat) 24 -> (((V 2%nat) - 96) + 12 <= (V 57%nat) \/ (V 57%nat) + 24 <= ((V 2%nat) - 96)) -> ((V 57%nat) + 24 <= 80496 \/ 80496 + 512 <= (V 57%nat)) -> u16_at M ((2 * (V 60%nat)) + 80496) (V 72%nat) ->
  u16_at M ((2 * (V 61%nat)) + 80496) (V 73%nat) -> u16_at M ((2 * (V 62%nat)) + 80496) (V 74%nat) -> u16_at M ((2 * (V 63%nat)) + 80496) (V 75%nat) -> u16_at M ((2 * (V 64%nat)) + 80496) (V 76%nat) ->
  u16_at M ((2 * (V 65%nat)) + 80496) (V 77%nat) -> u16_at M ((2 * (V 66%nat)) + 80496) (V 78%nat) -> u16_at M ((2 * (V 67%nat)) + 80496) (V 79%nat) -> u16_at M ((2 * (V 68%nat)) + 80496) (V 80%nat) ->
  u16_at M ((2 * (V 69%nat)) + 80496) (V 81%nat) -> u16_at M ((2 * (V 70%nat)) + 80496) (V 82%nat) -> u16_at M ((2 * (V 71%nat)) + 80496) (V 83%nat) -> 0 <= (V 72%nat) <= 65535 ->
  0 <= (V 73%nat) <= 65535 -> 0 <= (V 74%nat) <= 65535 -> 0 <= (V 75%nat) <= 65535 -> 0 <= (V 76%nat) <= 65535 ->
  0 <= (V 77%nat) <= 65535 -> 0 <= (V 78%nat) <= 65535 -> 0 <= (V 79%nat) <= 65535 -> 0 <= (V 80%nat) <= 65535 ->
  0 <= (V 81%nat) <= 65535 -> 0 <= (V 82%nat) <= 65535 -> 0 <= (V 83%nat) <= 65535 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 57%nat) + 0) <= bv_unsigned a < ((V 57%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 57%nat) + 0) <= i < ((V 57%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39bf8 M) (st fx' R' 0x37c60 M')
        /\ (forall x, In x KS_vlOH -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 80496
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551593
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551604
        /\ rdn RSEGS M' (Z_to_bv 64 ((V 57%nat) + 22)) 2 = Some (word_to_le_bytes 2 (v_lh (Z_to_bv 64 (V 83%nat))))
        /\ rdn RSEGS M' (Z_to_bv 64 ((V 57%nat) + 20)) 2 = Some (word_to_le_bytes 2 (v_lh (Z_to_bv 64 (V 82%nat))))
        /\ rdn RSEGS M' (Z_to_bv 64 ((V 57%nat) + 18)) 2 = Some (word_to_le_bytes 2 (v_lh (Z_to_bv 64 (V 81%nat))))
        /\ rdn RSEGS M' (Z_to_bv 64 ((V 57%nat) + 16)) 2 = Some (word_to_le_bytes 2 (v_lh (Z_to_bv 64 (V 80%nat))))
        /\ rdn RSEGS M' (Z_to_bv 64 ((V 57%nat) + 14)) 2 = Some (word_to_le_bytes 2 (v_lh (Z_to_bv 64 (V 79%nat))))
        /\ rdn RSEGS M' (Z_to_bv 64 ((V 57%nat) + 12)) 2 = Some (word_to_le_bytes 2 (v_lh (Z_to_bv 64 (V 78%nat))))
        /\ rdn RSEGS M' (Z_to_bv 64 ((V 57%nat) + 10)) 2 = Some (word_to_le_bytes 2 (v_lh (Z_to_bv 64 (V 77%nat))))
        /\ rdn RSEGS M' (Z_to_bv 64 ((V 57%nat) + 8)) 2 = Some (word_to_le_bytes 2 (v_lh (Z_to_bv 64 (V 76%nat))))
        /\ rdn RSEGS M' (Z_to_bv 64 ((V 57%nat) + 6)) 2 = Some (word_to_le_bytes 2 (v_lh (Z_to_bv 64 (V 75%nat))))
        /\ rdn RSEGS M' (Z_to_bv 64 ((V 57%nat) + 4)) 2 = Some (word_to_le_bytes 2 (v_lh (Z_to_bv 64 (V 74%nat))))
        /\ rdn RSEGS M' (Z_to_bv 64 ((V 57%nat) + 2)) 2 = Some (word_to_le_bytes 2 (v_lh (Z_to_bv 64 (V 73%nat))))
        /\ rdn RSEGS M' (Z_to_bv 64 ((V 57%nat) + 0)) 2 = Some (word_to_le_bytes 2 (v_lh (Z_to_bv 64 (V 72%nat))))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 pvzI22 pvzI23 pvzI24 pvzI25 pvzI26 pvzI27 pvzI28 pvzI29 G1 G2 G8 G9 G10 G11 G18 pvzI30 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 pvzI31 pvzI32 pvzI33 pvzI34 pvzI35 pvzI36 pvzI37 pvzI38 pvzI39 pvzI40 pvzI41 pvzI42 pvzI43 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 pvzI44 pvzI45 pvzI46 pvzI47 pvzI48 pvzI49 pvzI50 pvzI51 pvzI52 pvzI53 pvzI54 pvzI55.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV57l; move HV57l before pvzI5; pose proof (proj2 pvzI5) as HV57r; move HV57r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV60l; move HV60l before pvzI6; pose proof (proj2 pvzI6) as HV60r; move HV60r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV61l; move HV61l before pvzI7; pose proof (proj2 pvzI7) as HV61r; move HV61r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV62l; move HV62l before pvzI8; pose proof (proj2 pvzI8) as HV62r; move HV62r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV63l; move HV63l before pvzI9; pose proof (proj2 pvzI9) as HV63r; move HV63r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV64l; move HV64l before pvzI10; pose proof (proj2 pvzI10) as HV64r; move HV64r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV65l; move HV65l before pvzI11; pose proof (proj2 pvzI11) as HV65r; move HV65r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV66l; move HV66l before pvzI12; pose proof (proj2 pvzI12) as HV66r; move HV66r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV67l; move HV67l before pvzI13; pose proof (proj2 pvzI13) as HV67r; move HV67r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV68l; move HV68l before pvzI14; pose proof (proj2 pvzI14) as HV68r; move HV68r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV69l; move HV69l before pvzI15; pose proof (proj2 pvzI15) as HV69r; move HV69r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV70l; move HV70l before pvzI16; pose proof (proj2 pvzI16) as HV70r; move HV70r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV71l; move HV71l before pvzI17; pose proof (proj2 pvzI17) as HV71r; move HV71r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV72l; move HV72l before pvzI18; pose proof (proj2 pvzI18) as HV72r; move HV72r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV73l; move HV73l before pvzI19; pose proof (proj2 pvzI19) as HV73r; move HV73r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV74l; move HV74l before pvzI20; pose proof (proj2 pvzI20) as HV74r; move HV74r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV75l; move HV75l before pvzI21; pose proof (proj2 pvzI21) as HV75r; move HV75r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as HV76l; move HV76l before pvzI22; pose proof (proj2 pvzI22) as HV76r; move HV76r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as HV77l; move HV77l before pvzI23; pose proof (proj2 pvzI23) as HV77r; move HV77r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as HV78l; move HV78l before pvzI24; pose proof (proj2 pvzI24) as HV78r; move HV78r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as HV79l; move HV79l before pvzI25; pose proof (proj2 pvzI25) as HV79r; move HV79r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as HV80l; move HV80l before pvzI26; pose proof (proj2 pvzI26) as HV80r; move HV80r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as HV81l; move HV81l before pvzI27; pose proof (proj2 pvzI27) as HV81r; move HV81r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as HV82l; move HV82l before pvzI28; pose proof (proj2 pvzI28) as HV82r; move HV82r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as HV83l; move HV83l before pvzI29; pose proof (proj2 pvzI29) as HV83r; move HV83r before pvzI29; clear pvzI29. pose proof (proj1 pvzI30) as K0l; move K0l before pvzI30; pose proof (proj2 pvzI30) as K0r; move K0r before pvzI30; clear pvzI30. pose proof (proj1 pvzI31) as K14l; move K14l before pvzI31; pose proof (proj2 pvzI31) as K14r; move K14r before pvzI31; clear pvzI31. pose proof (proj1 pvzI32) as K15l; move K15l before pvzI32; pose proof (proj2 pvzI32) as K15r; move K15r before pvzI32; clear pvzI32. pose proof (proj1 pvzI33) as K16l; move K16l before pvzI33; pose proof (proj2 pvzI33) as K16r; move K16r before pvzI33; clear pvzI33. pose proof (proj1 pvzI34) as K17l; move K17l before pvzI34; pose proof (proj2 pvzI34) as K17r; move K17r before pvzI34; clear pvzI34. pose proof (proj1 pvzI35) as K18l; move K18l before pvzI35; pose proof (proj2 pvzI35) as K18r; move K18r before pvzI35; clear pvzI35. pose proof (proj1 pvzI36) as K19l; move K19l before pvzI36; pose proof (proj2 pvzI36) as K19r; move K19r before pvzI36; clear pvzI36. pose proof (proj1 pvzI37) as K20l; move K20l before pvzI37; pose proof (proj2 pvzI37) as K20r; move K20r before pvzI37; clear pvzI37. pose proof (proj1 pvzI38) as K21l; move K21l before pvzI38; pose proof (proj2 pvzI38) as K21r; move K21r before pvzI38; clear pvzI38. pose proof (proj1 pvzI39) as K22l; move K22l before pvzI39; pose proof (proj2 pvzI39) as K22r; move K22r before pvzI39; clear pvzI39. pose proof (proj1 pvzI40) as K23l; move K23l before pvzI40; pose proof (proj2 pvzI40) as K23r; move K23r before pvzI40; clear pvzI40. pose proof (proj1 pvzI41) as K24l; move K24l before pvzI41; pose proof (proj2 pvzI41) as K24r; move K24r before pvzI41; clear pvzI41. pose proof (proj1 pvzI42) as K25l; move K25l before pvzI42; pose proof (proj2 pvzI42) as K25r; move K25r before pvzI42; clear pvzI42. pose proof (proj1 pvzI43) as K26l; move K26l before pvzI43; pose proof (proj2 pvzI43) as K26r; move K26r before pvzI43; clear pvzI43. pose proof (proj1 pvzI44) as K43l; move K43l before pvzI44; pose proof (proj2 pvzI44) as K43r; move K43r before pvzI44; clear pvzI44. pose proof (proj1 pvzI45) as K44l; move K44l before pvzI45; pose proof (proj2 pvzI45) as K44r; move K44r before pvzI45; clear pvzI45. pose proof (proj1 pvzI46) as K45l; move K45l before pvzI46; pose proof (proj2 pvzI46) as K45r; move K45r before pvzI46; clear pvzI46. pose proof (proj1 pvzI47) as K46l; move K46l before pvzI47; pose proof (proj2 pvzI47) as K46r; move K46r before pvzI47; clear pvzI47. pose proof (proj1 pvzI48) as K47l; move K47l before pvzI48; pose proof (proj2 pvzI48) as K47r; move K47r before pvzI48; clear pvzI48. pose proof (proj1 pvzI49) as K48l; move K48l before pvzI49; pose proof (proj2 pvzI49) as K48r; move K48r before pvzI49; clear pvzI49. pose proof (proj1 pvzI50) as K49l; move K49l before pvzI50; pose proof (proj2 pvzI50) as K49r; move K49r before pvzI50; clear pvzI50. pose proof (proj1 pvzI51) as K50l; move K50l before pvzI51; pose proof (proj2 pvzI51) as K50r; move K50r before pvzI51; clear pvzI51. pose proof (proj1 pvzI52) as K51l; move K51l before pvzI52; pose proof (proj2 pvzI52) as K51r; move K51r before pvzI52; clear pvzI52. pose proof (proj1 pvzI53) as K52l; move K52l before pvzI53; pose proof (proj2 pvzI53) as K52r; move K52r before pvzI53; clear pvzI53. pose proof (proj1 pvzI54) as K53l; move K53l before pvzI54; pose proof (proj2 pvzI54) as K53r; move K53r before pvzI54; clear pvzI54. pose proof (proj1 pvzI55) as K54l; move K54l before pvzI55; pose proof (proj2 pvzI55) as K54r; move K54r before pvzI55; clear pvzI55.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_61 := V 61%nat) in *. set (vz_62 := V 62%nat) in *. set (vz_63 := V 63%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *. set (vz_76 := V 76%nat) in *. set (vz_77 := V 77%nat) in *. set (vz_78 := V 78%nat) in *. set (vz_79 := V 79%nat) in *. set (vz_80 := V 80%nat) in *. set (vz_81 := V 81%nat) in *. set (vz_82 := V 82%nat) in *. set (vz_83 := V 83%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 57%nat => Z_to_bv 64 vz_57 | 60%nat => Z_to_bv 64 vz_60 | 61%nat => Z_to_bv 64 vz_61 | 62%nat => Z_to_bv 64 vz_62 | 63%nat => Z_to_bv 64 vz_63 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | 76%nat => Z_to_bv 64 vz_76 | 77%nat => Z_to_bv 64 vz_77 | 78%nat => Z_to_bv 64 vz_78 | 79%nat => Z_to_bv 64 vz_79 | 80%nat => Z_to_bv 64 vz_80 | 81%nat => Z_to_bv 64 vz_81 | 82%nat => Z_to_bv 64 vz_82 | 83%nat => Z_to_bv 64 vz_83 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | 57%nat => vz_57 | 60%nat => vz_60 | 61%nat => vz_61 | 62%nat => vz_62 | 63%nat => vz_63 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | 76%nat => vz_76 | 77%nat => vz_77 | 78%nat => vz_78 | 79%nat => vz_79 | 80%nat => vz_80 | 81%nat => vz_81 | 82%nat => vz_82 | 83%nat => vz_83 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 84%nat. }
  assert (HR: regs_ok E PvlOH.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlOH.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlOH.kn0).
  { unfold know_ok, PvlOH.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K29) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K29) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K29) | evalEk ZA ltac:(clear - HV60l HV60r K14l K14r) | clear - HV2l HV2r K0l K0r K29; lia | clear - HV2l HV2r K0l K0r K29; lia | byte_tac ltac:(clear - HV60l HV60r K14l K14r) | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K29) | evalEk ZA ltac:(clear - HV61l HV61r K15l K15r) | clear - HV2l HV2r K0l K0r K29; lia | clear - HV2l HV2r K0l K0r K29; lia | byte_tac ltac:(clear - HV61l HV61r K15l K15r) | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K29) | evalEk ZA ltac:(clear - HV62l HV62r K16l K16r) | clear - HV2l HV2r K0l K0r K29; lia | clear - HV2l HV2r K0l K0r K29; lia | byte_tac ltac:(clear - HV62l HV62r K16l K16r) | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K29) | evalEk ZA ltac:(clear - HV63l HV63r K17l K17r) | clear - HV2l HV2r K0l K0r K29; lia | clear - HV2l HV2r K0l K0r K29; lia | byte_tac ltac:(clear - HV63l HV63r K17l K17r) | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K29) | evalEk ZA ltac:(clear - HV64l HV64r K18l K18r) | clear - HV2l HV2r K0l K0r K29; lia | clear - HV2l HV2r K0l K0r K29; lia | byte_tac ltac:(clear - HV64l HV64r K18l K18r) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K29) | evalEk ZA ltac:(clear - HV65l HV65r K19l K19r) | clear - HV2l HV2r K0l K0r K29; lia | clear - HV2l HV2r K0l K0r K29; lia | byte_tac ltac:(clear - HV65l HV65r K19l K19r) | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K29) | evalEk ZA ltac:(clear - HV66l HV66r K20l K20r) | clear - HV2l HV2r K0l K0r K29; lia | clear - HV2l HV2r K0l K0r K29; lia | byte_tac ltac:(clear - HV66l HV66r K20l K20r) | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K29) | evalEk ZA ltac:(clear - HV67l HV67r K21l K21r) | clear - HV2l HV2r K0l K0r K29; lia | clear - HV2l HV2r K0l K0r K29; lia | byte_tac ltac:(clear - HV67l HV67r K21l K21r) | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K29) | evalEk ZA ltac:(clear - HV68l HV68r K22l K22r) | clear - HV2l HV2r K0l K0r K29; lia | clear - HV2l HV2r K0l K0r K29; lia | byte_tac ltac:(clear - HV68l HV68r K22l K22r) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K29) | evalEk ZA ltac:(clear - HV69l HV69r K23l K23r) | clear - HV2l HV2r K0l K0r K29; lia | clear - HV2l HV2r K0l K0r K29; lia | byte_tac ltac:(clear - HV69l HV69r K23l K23r) | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K29) | evalEk ZA ltac:(clear - HV70l HV70r K24l K24r) | clear - HV2l HV2r K0l K0r K29; lia | clear - HV2l HV2r K0l K0r K29; lia | byte_tac ltac:(clear - HV70l HV70r K24l K24r) | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K29) | evalEk ZA ltac:(clear - HV71l HV71r K25l K25r) | clear - HV2l HV2r K0l K0r K29; lia | clear - HV2l HV2r K0l K0r K29; lia | byte_tac ltac:(clear - HV71l HV71r K25l K25r) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV60l HV60r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV61l HV61r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV63l HV63r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV64l HV64r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV65l HV65r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV66l HV66r K20l K20r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV67l HV67r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV68l HV68r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV69l HV69r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV70l HV70r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV71l HV71r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV57l HV57r K26l K26r K29 K30) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV57l HV57r K26l K26r K29 K30) | clear; lia | exact K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk ZA ltac:(clear) | clear - HV57l HV57r K26l K26r K29 K30; lia | clear - HV57l HV57r K26l K26r K29 K30; lia | clear - HV57l HV57r K26l K26r K29 K30; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K29) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply kentry_KWord2a; [evalEk ZA ltac:(clear - HV60l HV60r K14l K14r) | evalEk ZA ltac:(clear - HV72l HV72r K43l K43r) | clear - HV60l HV60r K14l K14r; lia | clear - HV60l HV60r K14l K14r; lia | exactA K31]. }
    apply Forall_cons. { eapply kentry_KWord2a; [evalEk ZA ltac:(clear - HV61l HV61r K15l K15r) | evalEk ZA ltac:(clear - HV73l HV73r K44l K44r) | clear - HV61l HV61r K15l K15r; lia | clear - HV61l HV61r K15l K15r; lia | exactA K32]. }
    apply Forall_cons. { eapply kentry_KWord2a; [evalEk ZA ltac:(clear - HV62l HV62r K16l K16r) | evalEk ZA ltac:(clear - HV74l HV74r K45l K45r) | clear - HV62l HV62r K16l K16r; lia | clear - HV62l HV62r K16l K16r; lia | exactA K33]. }
    apply Forall_cons. { eapply kentry_KWord2a; [evalEk ZA ltac:(clear - HV63l HV63r K17l K17r) | evalEk ZA ltac:(clear - HV75l HV75r K46l K46r) | clear - HV63l HV63r K17l K17r; lia | clear - HV63l HV63r K17l K17r; lia | exactA K34]. }
    apply Forall_cons. { eapply kentry_KWord2a; [evalEk ZA ltac:(clear - HV64l HV64r K18l K18r) | evalEk ZA ltac:(clear - HV76l HV76r K47l K47r) | clear - HV64l HV64r K18l K18r; lia | clear - HV64l HV64r K18l K18r; lia | exactA K35]. }
    apply Forall_cons. { eapply kentry_KWord2a; [evalEk ZA ltac:(clear - HV65l HV65r K19l K19r) | evalEk ZA ltac:(clear - HV77l HV77r K48l K48r) | clear - HV65l HV65r K19l K19r; lia | clear - HV65l HV65r K19l K19r; lia | exactA K36]. }
    apply Forall_cons. { eapply kentry_KWord2a; [evalEk ZA ltac:(clear - HV66l HV66r K20l K20r) | evalEk ZA ltac:(clear - HV78l HV78r K49l K49r) | clear - HV66l HV66r K20l K20r; lia | clear - HV66l HV66r K20l K20r; lia | exactA K37]. }
    apply Forall_cons. { eapply kentry_KWord2a; [evalEk ZA ltac:(clear - HV67l HV67r K21l K21r) | evalEk ZA ltac:(clear - HV79l HV79r K50l K50r) | clear - HV67l HV67r K21l K21r; lia | clear - HV67l HV67r K21l K21r; lia | exactA K38]. }
    apply Forall_cons. { eapply kentry_KWord2a; [evalEk ZA ltac:(clear - HV68l HV68r K22l K22r) | evalEk ZA ltac:(clear - HV80l HV80r K51l K51r) | clear - HV68l HV68r K22l K22r; lia | clear - HV68l HV68r K22l K22r; lia | exactA K39]. }
    apply Forall_cons. { eapply kentry_KWord2a; [evalEk ZA ltac:(clear - HV69l HV69r K23l K23r) | evalEk ZA ltac:(clear - HV81l HV81r K52l K52r) | clear - HV69l HV69r K23l K23r; lia | clear - HV69l HV69r K23l K23r; lia | exactA K40]. }
    apply Forall_cons. { eapply kentry_KWord2a; [evalEk ZA ltac:(clear - HV70l HV70r K24l K24r) | evalEk ZA ltac:(clear - HV82l HV82r K53l K53r) | clear - HV70l HV70r K24l K24r; lia | clear - HV70l HV70r K24l K24r; lia | exactA K41]. }
    apply Forall_cons. { eapply kentry_KWord2a; [evalEk ZA ltac:(clear - HV71l HV71r K25l K25r) | evalEk ZA ltac:(clear - HV83l HV83r K54l K54r) | clear - HV71l HV71r K25l K25r; lia | clear - HV71l HV71r K25l K25r; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV72l HV72r K43l K43r) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV73l HV73r K44l K44r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K45l K45r) | exact (conj K45l K45r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K46l K46r) | exact (conj K46l K46r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV76l HV76r K47l K47r) | exact (conj K47l K47r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV77l HV77r K48l K48r) | exact (conj K48l K48r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV78l HV78r K49l K49r) | exact (conj K49l K49r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K50l K50r) | exact (conj K50l K50r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV80l HV80r K51l K51r) | exact (conj K51l K51r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV81l HV81r K52l K52r) | exact (conj K52l K52r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV82l HV82r K53l K53r) | exact (conj K53l K53r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV83l HV83r K54l K54r) | exact (conj K54l K54r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlOH.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlOH.NX0 with 84%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_57 + 0) <= bv_unsigned a < (vz_57 + 0) + 24) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvlOH.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk' ZA Hag ltac:(clear) | clear - HV57l HV57r K26l K26r K29 K30 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlOH.ps0) with 0x37c60 in Hms. change (SR.ps_regs PvlOH.ps0) with (map (fun i => (i, nth i PvlOH.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlOH.ps0) with PvlOH.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlOH.regs0 PvlOH.regs_out0 84 KS_vlOH KS_vlOH_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlOH.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvlOH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlOH.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlOH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlOH.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvlOH.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply rd2_of_KWord2x; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk' ZA Hag ltac:(clear - HV83l HV83r K54l K54r) | clear - K54l K54r; lia | clear; lia]. }
  split. { eapply rd2_of_KWord2x; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk' ZA Hag ltac:(clear - HV82l HV82r K53l K53r) | clear - K53l K53r; lia | clear; lia]. }
  split. { eapply rd2_of_KWord2x; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk' ZA Hag ltac:(clear - HV81l HV81r K52l K52r) | clear - K52l K52r; lia | clear; lia]. }
  split. { eapply rd2_of_KWord2x; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk' ZA Hag ltac:(clear - HV80l HV80r K51l K51r) | clear - K51l K51r; lia | clear; lia]. }
  split. { eapply rd2_of_KWord2x; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk' ZA Hag ltac:(clear - HV79l HV79r K50l K50r) | clear - K50l K50r; lia | clear; lia]. }
  split. { eapply rd2_of_KWord2x; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk' ZA Hag ltac:(clear - HV78l HV78r K49l K49r) | clear - K49l K49r; lia | clear; lia]. }
  split. { eapply rd2_of_KWord2x; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk' ZA Hag ltac:(clear - HV77l HV77r K48l K48r) | clear - K48l K48r; lia | clear; lia]. }
  split. { eapply rd2_of_KWord2x; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk' ZA Hag ltac:(clear - HV76l HV76r K47l K47r) | clear - K47l K47r; lia | clear; lia]. }
  split. { eapply rd2_of_KWord2x; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk' ZA Hag ltac:(clear - HV75l HV75r K46l K46r) | clear - K46l K46r; lia | clear; lia]. }
  split. { eapply rd2_of_KWord2x; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk' ZA Hag ltac:(clear - HV74l HV74r K45l K45r) | clear - K45l K45r; lia | clear; lia]. }
  split. { eapply rd2_of_KWord2x; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk' ZA Hag ltac:(clear - HV73l HV73r K44l K44r) | clear - K44l K44r; lia | clear; lia]. }
  eapply rd2_of_KWord2x; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV57l HV57r K26l K26r K29 K30) | evalEk' ZA Hag ltac:(clear - HV72l HV72r K43l K43r) | clear - K43l K43r; lia | clear; lia].
Qed.

End PNSRVOP.
