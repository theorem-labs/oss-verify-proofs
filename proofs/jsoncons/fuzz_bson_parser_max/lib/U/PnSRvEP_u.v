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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_vlE_u LibSegBs_vlJ1_u LibSegBs_vlJ2_u LibSegBs_vlJ3_u LibSegBs_vlJ4_u LibSegBs_vlJ5_u LibSegBs_vlJ6_u LibSegBs_vlJ7_u LibSegBs_vlJ8_u LibSegBs_vlJ9_u LibSegBs_vlJ10_u LibSegBs_vlJ11_u LibSegBs_vlJ12_u LibSegBs_vlJ13_u LibSegBs_vlJ14_u LibSegBs_vlJ15_u LibSegBs_vlJ16_u LibSegBs_vlJ17_u LibSegBs_vlJ18_u LibSegBs_vlJ19_u LibSegBs_vlJ127_u LibSegBs_vlJ255_u LibSegBs_vlJz_u LibSegBs_vlJr1_u LibSegBs_vlJr2_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRVEP.
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
Module PvlE := LibSegBs_vlE_u.
Definition KS_vlE : list nat := Eval vm_compute in (BG.kept_list 72 PvlE.regs0 PvlE.regs_out0).
Lemma KS_vlE_ok : BG.kept_ok 72 PvlE.regs0 PvlE.regs_out0 KS_vlE = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 36%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> 0 <= (V 35%nat) <= 255 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 48) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 48) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x375ec M) (st fx' R' 0x3761c M')
        /\ (forall x, In x KS_vlE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 35%nat) - 1)
        /\ getr R' (reg 13) = Z_to_bv 64 18
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 G12 G13 pvzI6 K1 K2 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlE.kn0).
  { unfold know_ok, PvlE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlE.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 48) <= bv_unsigned a < (vz_2 - 48) + 48) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvlE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlE.ps0) with 0x3761c in Hms. change (SR.ps_regs PvlE.ps0) with (map (fun i => (i, nth i PvlE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlE.ps0) with PvlE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlE.regs0 PvlE.regs_out0 72 KS_vlE KS_vlE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvlE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlE.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvlE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlE.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvlE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlE.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlE.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvlE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvlE.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvlE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ1 := LibSegBs_vlJ1_u.
Definition KS_vlJ1 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ1.regs0 PvlJ1.regs_out0).
Lemma KS_vlJ1_ok : BG.kept_ok 72 PvlJ1.regs0 PvlJ1.regs_out0 KS_vlJ1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 0 -> getr R (reg 12) = Z_to_bv 64 1 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x3763c M')
        /\ (forall x, In x KS_vlJ1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 226876
        /\ getr R' (reg 11) = Z_to_bv 64 147224).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ1.kn0).
  { unfold know_ok, PvlJ1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ1.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ1.ps0) with 0x3763c in Hms. change (SR.ps_regs PvlJ1.ps0) with (map (fun i => (i, nth i PvlJ1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ1.ps0) with PvlJ1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ1.regs0 PvlJ1.regs_out0 72 KS_vlJ1 KS_vlJ1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ2 := LibSegBs_vlJ2_u.
Definition KS_vlJ2 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ2.regs0 PvlJ2.regs_out0).
Lemma KS_vlJ2_ok : BG.kept_ok 72 PvlJ2.regs0 PvlJ2.regs_out0 KS_vlJ2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 1 -> getr R (reg 12) = Z_to_bv 64 2 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x376bc M')
        /\ (forall x, In x KS_vlJ2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 227004
        /\ getr R' (reg 11) = Z_to_bv 64 147352).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ2.kn0).
  { unfold know_ok, PvlJ2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ2.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ2.ps0) with 0x376bc in Hms. change (SR.ps_regs PvlJ2.ps0) with (map (fun i => (i, nth i PvlJ2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ2.ps0) with PvlJ2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ2.regs0 PvlJ2.regs_out0 72 KS_vlJ2 KS_vlJ2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ3 := LibSegBs_vlJ3_u.
Definition KS_vlJ3 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ3.regs0 PvlJ3.regs_out0).
Lemma KS_vlJ3_ok : BG.kept_ok 72 PvlJ3.regs0 PvlJ3.regs_out0 KS_vlJ3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 2 -> getr R (reg 12) = Z_to_bv 64 3 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x377d8 M')
        /\ (forall x, In x KS_vlJ3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 227288
        /\ getr R' (reg 11) = Z_to_bv 64 147636).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ3.kn0).
  { unfold know_ok, PvlJ3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ3.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ3.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ3.ps0) with 0x377d8 in Hms. change (SR.ps_regs PvlJ3.ps0) with (map (fun i => (i, nth i PvlJ3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ3.ps0) with PvlJ3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ3.regs0 PvlJ3.regs_out0 72 KS_vlJ3 KS_vlJ3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ3.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ4 := LibSegBs_vlJ4_u.
Definition KS_vlJ4 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ4.regs0 PvlJ4.regs_out0).
Lemma KS_vlJ4_ok : BG.kept_ok 72 PvlJ4.regs0 PvlJ4.regs_out0 KS_vlJ4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ4_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 3 -> getr R (reg 12) = Z_to_bv 64 4 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x37894 M')
        /\ (forall x, In x KS_vlJ4 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 227476
        /\ getr R' (reg 11) = Z_to_bv 64 147824).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ4.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ4.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ4.kn0).
  { unfold know_ok, PvlJ4.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ4.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ4.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ4.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ4.ps0) with 0x37894 in Hms. change (SR.ps_regs PvlJ4.ps0) with (map (fun i => (i, nth i PvlJ4.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ4.ps0) with PvlJ4.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ4.regs0 PvlJ4.regs_out0 72 KS_vlJ4 KS_vlJ4_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ4.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ4.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ4.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ4.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ5 := LibSegBs_vlJ5_u.
Definition KS_vlJ5 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ5.regs0 PvlJ5.regs_out0).
Lemma KS_vlJ5_ok : BG.kept_ok 72 PvlJ5.regs0 PvlJ5.regs_out0 KS_vlJ5 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ5_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 4 -> getr R (reg 12) = Z_to_bv 64 5 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x378c0 M')
        /\ (forall x, In x KS_vlJ5 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 227520
        /\ getr R' (reg 11) = Z_to_bv 64 147868).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ5.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ5.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ5.kn0).
  { unfold know_ok, PvlJ5.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ5.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ5.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ5.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ5.ps0) with 0x378c0 in Hms. change (SR.ps_regs PvlJ5.ps0) with (map (fun i => (i, nth i PvlJ5.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ5.ps0) with PvlJ5.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ5.regs0 PvlJ5.regs_out0 72 KS_vlJ5 KS_vlJ5_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ5.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ5.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ5.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ5.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ6 := LibSegBs_vlJ6_u.
Definition KS_vlJ6 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ6.regs0 PvlJ6.regs_out0).
Lemma KS_vlJ6_ok : BG.kept_ok 72 PvlJ6.regs0 PvlJ6.regs_out0 KS_vlJ6 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ6_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 5 -> getr R (reg 12) = Z_to_bv 64 6 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x37a90 M')
        /\ (forall x, In x KS_vlJ6 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 227984
        /\ getr R' (reg 11) = Z_to_bv 64 148332).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ6.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ6.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ6.kn0).
  { unfold know_ok, PvlJ6.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ6.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ6.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ6.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ6.ps0) with 0x37a90 in Hms. change (SR.ps_regs PvlJ6.ps0) with (map (fun i => (i, nth i PvlJ6.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ6.ps0) with PvlJ6.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ6.regs0 PvlJ6.regs_out0 72 KS_vlJ6 KS_vlJ6_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ6.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ6.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ6.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ6.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ7 := LibSegBs_vlJ7_u.
Definition KS_vlJ7 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ7.regs0 PvlJ7.regs_out0).
Lemma KS_vlJ7_ok : BG.kept_ok 72 PvlJ7.regs0 PvlJ7.regs_out0 KS_vlJ7 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ7_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 6 -> getr R (reg 12) = Z_to_bv 64 7 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x379a4 M')
        /\ (forall x, In x KS_vlJ7 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 227748
        /\ getr R' (reg 11) = Z_to_bv 64 148096).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ7.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ7.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ7.kn0).
  { unfold know_ok, PvlJ7.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ7.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ7.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ7.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ7.ps0) with 0x379a4 in Hms. change (SR.ps_regs PvlJ7.ps0) with (map (fun i => (i, nth i PvlJ7.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ7.ps0) with PvlJ7.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ7.regs0 PvlJ7.regs_out0 72 KS_vlJ7 KS_vlJ7_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ7.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ7.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ7.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ7.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ8 := LibSegBs_vlJ8_u.
Definition KS_vlJ8 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ8.regs0 PvlJ8.regs_out0).
Lemma KS_vlJ8_ok : BG.kept_ok 72 PvlJ8.regs0 PvlJ8.regs_out0 KS_vlJ8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ8_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 7 -> getr R (reg 12) = Z_to_bv 64 8 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x37aa4 M')
        /\ (forall x, In x KS_vlJ8 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 228004
        /\ getr R' (reg 11) = Z_to_bv 64 148352).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ8.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ8.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ8.kn0).
  { unfold know_ok, PvlJ8.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ8.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ8.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ8.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ8.ps0) with 0x37aa4 in Hms. change (SR.ps_regs PvlJ8.ps0) with (map (fun i => (i, nth i PvlJ8.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ8.ps0) with PvlJ8.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ8.regs0 PvlJ8.regs_out0 72 KS_vlJ8 KS_vlJ8_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ8.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ8.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ8.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ8.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ9 := LibSegBs_vlJ9_u.
Definition KS_vlJ9 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ9.regs0 PvlJ9.regs_out0).
Lemma KS_vlJ9_ok : BG.kept_ok 72 PvlJ9.regs0 PvlJ9.regs_out0 KS_vlJ9 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ9_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 8 -> getr R (reg 12) = Z_to_bv 64 9 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x37804 M')
        /\ (forall x, In x KS_vlJ9 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 227332
        /\ getr R' (reg 11) = Z_to_bv 64 147680).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ9.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ9.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ9.kn0).
  { unfold know_ok, PvlJ9.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ9.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ9.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ9.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ9.ps0) with 0x37804 in Hms. change (SR.ps_regs PvlJ9.ps0) with (map (fun i => (i, nth i PvlJ9.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ9.ps0) with PvlJ9.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ9.regs0 PvlJ9.regs_out0 72 KS_vlJ9 KS_vlJ9_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ9.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ9.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ9.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ9.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ10 := LibSegBs_vlJ10_u.
Definition KS_vlJ10 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ10.regs0 PvlJ10.regs_out0).
Lemma KS_vlJ10_ok : BG.kept_ok 72 PvlJ10.regs0 PvlJ10.regs_out0 KS_vlJ10 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ10_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 9 -> getr R (reg 12) = Z_to_bv 64 10 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x37b14 M')
        /\ (forall x, In x KS_vlJ10 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 228116
        /\ getr R' (reg 11) = Z_to_bv 64 148464).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ10.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ10.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ10.kn0).
  { unfold know_ok, PvlJ10.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ10.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ10.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ10.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ10.ps0) with 0x37b14 in Hms. change (SR.ps_regs PvlJ10.ps0) with (map (fun i => (i, nth i PvlJ10.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ10.ps0) with PvlJ10.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ10.regs0 PvlJ10.regs_out0 72 KS_vlJ10 KS_vlJ10_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ10.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ10.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ10.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ10.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ11 := LibSegBs_vlJ11_u.
Definition KS_vlJ11 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ11.regs0 PvlJ11.regs_out0).
Lemma KS_vlJ11_ok : BG.kept_ok 72 PvlJ11.regs0 PvlJ11.regs_out0 KS_vlJ11 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ11_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 10 -> getr R (reg 12) = Z_to_bv 64 11 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x377c4 M')
        /\ (forall x, In x KS_vlJ11 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 227268
        /\ getr R' (reg 11) = Z_to_bv 64 147616).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ11.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ11.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ11.kn0).
  { unfold know_ok, PvlJ11.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ11.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ11.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ11.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ11.ps0) with 0x377c4 in Hms. change (SR.ps_regs PvlJ11.ps0) with (map (fun i => (i, nth i PvlJ11.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ11.ps0) with PvlJ11.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ11.regs0 PvlJ11.regs_out0 72 KS_vlJ11 KS_vlJ11_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ11.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ11.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ11.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ12 := LibSegBs_vlJ12_u.
Definition KS_vlJ12 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ12.regs0 PvlJ12.regs_out0).
Lemma KS_vlJ12_ok : BG.kept_ok 72 PvlJ12.regs0 PvlJ12.regs_out0 KS_vlJ12 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ12_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 11 -> getr R (reg 12) = Z_to_bv 64 12 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x376f4 M')
        /\ (forall x, In x KS_vlJ12 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 227060
        /\ getr R' (reg 11) = Z_to_bv 64 147408).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ12.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ12.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ12.kn0).
  { unfold know_ok, PvlJ12.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ12.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ12.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ12.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ12.ps0) with 0x376f4 in Hms. change (SR.ps_regs PvlJ12.ps0) with (map (fun i => (i, nth i PvlJ12.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ12.ps0) with PvlJ12.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ12.regs0 PvlJ12.regs_out0 72 KS_vlJ12 KS_vlJ12_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ12.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ12.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ12.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ12.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ13 := LibSegBs_vlJ13_u.
Definition KS_vlJ13 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ13.regs0 PvlJ13.regs_out0).
Lemma KS_vlJ13_ok : BG.kept_ok 72 PvlJ13.regs0 PvlJ13.regs_out0 KS_vlJ13 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ13_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 12 -> getr R (reg 12) = Z_to_bv 64 13 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x37858 M')
        /\ (forall x, In x KS_vlJ13 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 227416
        /\ getr R' (reg 11) = Z_to_bv 64 147764).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ13.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ13.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ13.kn0).
  { unfold know_ok, PvlJ13.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ13.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ13.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ13.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ13.ps0) with 0x37858 in Hms. change (SR.ps_regs PvlJ13.ps0) with (map (fun i => (i, nth i PvlJ13.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ13.ps0) with PvlJ13.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ13.regs0 PvlJ13.regs_out0 72 KS_vlJ13 KS_vlJ13_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ13.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ13.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ13.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ13.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ14 := LibSegBs_vlJ14_u.
Definition KS_vlJ14 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ14.regs0 PvlJ14.regs_out0).
Lemma KS_vlJ14_ok : BG.kept_ok 72 PvlJ14.regs0 PvlJ14.regs_out0 KS_vlJ14 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ14_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 13 -> getr R (reg 12) = Z_to_bv 64 14 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x376bc M')
        /\ (forall x, In x KS_vlJ14 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 227004
        /\ getr R' (reg 11) = Z_to_bv 64 147352).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ14.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ14.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ14.kn0).
  { unfold know_ok, PvlJ14.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ14.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ14.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ14.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ14.ps0) with 0x376bc in Hms. change (SR.ps_regs PvlJ14.ps0) with (map (fun i => (i, nth i PvlJ14.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ14.ps0) with PvlJ14.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ14.regs0 PvlJ14.regs_out0 72 KS_vlJ14 KS_vlJ14_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ14.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ14.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ14.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ14.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ15 := LibSegBs_vlJ15_u.
Definition KS_vlJ15 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ15.regs0 PvlJ15.regs_out0).
Lemma KS_vlJ15_ok : BG.kept_ok 72 PvlJ15.regs0 PvlJ15.regs_out0 KS_vlJ15 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ15_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 14 -> getr R (reg 12) = Z_to_bv 64 15 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x376f4 M')
        /\ (forall x, In x KS_vlJ15 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 227060
        /\ getr R' (reg 11) = Z_to_bv 64 147408).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ15.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ15.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ15.kn0).
  { unfold know_ok, PvlJ15.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ15.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ15.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ15.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ15.ps0) with 0x376f4 in Hms. change (SR.ps_regs PvlJ15.ps0) with (map (fun i => (i, nth i PvlJ15.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ15.ps0) with PvlJ15.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ15.regs0 PvlJ15.regs_out0 72 KS_vlJ15 KS_vlJ15_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ15.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ15.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ15.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ15.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ16 := LibSegBs_vlJ16_u.
Definition KS_vlJ16 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ16.regs0 PvlJ16.regs_out0).
Lemma KS_vlJ16_ok : BG.kept_ok 72 PvlJ16.regs0 PvlJ16.regs_out0 KS_vlJ16 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ16_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 15 -> getr R (reg 12) = Z_to_bv 64 16 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x37b34 M')
        /\ (forall x, In x KS_vlJ16 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 228148
        /\ getr R' (reg 11) = Z_to_bv 64 148496).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ16.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ16.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ16.kn0).
  { unfold know_ok, PvlJ16.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ16.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ16.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ16.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ16.ps0) with 0x37b34 in Hms. change (SR.ps_regs PvlJ16.ps0) with (map (fun i => (i, nth i PvlJ16.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ16.ps0) with PvlJ16.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ16.regs0 PvlJ16.regs_out0 72 KS_vlJ16 KS_vlJ16_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ16.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ16.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ16.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ16.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ17 := LibSegBs_vlJ17_u.
Definition KS_vlJ17 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ17.regs0 PvlJ17.regs_out0).
Lemma KS_vlJ17_ok : BG.kept_ok 72 PvlJ17.regs0 PvlJ17.regs_out0 KS_vlJ17 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ17_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 16 -> getr R (reg 12) = Z_to_bv 64 17 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x37b84 M')
        /\ (forall x, In x KS_vlJ17 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 228228
        /\ getr R' (reg 11) = Z_to_bv 64 148576).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ17.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ17.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ17.kn0).
  { unfold know_ok, PvlJ17.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ17.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ17.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ17.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ17.ps0) with 0x37b84 in Hms. change (SR.ps_regs PvlJ17.ps0) with (map (fun i => (i, nth i PvlJ17.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ17.ps0) with PvlJ17.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ17.regs0 PvlJ17.regs_out0 72 KS_vlJ17 KS_vlJ17_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ17.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ17.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ17.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ17.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ18 := LibSegBs_vlJ18_u.
Definition KS_vlJ18 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ18.regs0 PvlJ18.regs_out0).
Lemma KS_vlJ18_ok : BG.kept_ok 72 PvlJ18.regs0 PvlJ18.regs_out0 KS_vlJ18 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ18_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 17 -> getr R (reg 12) = Z_to_bv 64 18 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x37708 M')
        /\ (forall x, In x KS_vlJ18 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 227080
        /\ getr R' (reg 11) = Z_to_bv 64 147428).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ18.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ18.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ18.kn0).
  { unfold know_ok, PvlJ18.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ18.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ18.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ18.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ18.ps0) with 0x37708 in Hms. change (SR.ps_regs PvlJ18.ps0) with (map (fun i => (i, nth i PvlJ18.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ18.ps0) with PvlJ18.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ18.regs0 PvlJ18.regs_out0 72 KS_vlJ18 KS_vlJ18_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ18.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ18.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ18.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ18.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ19 := LibSegBs_vlJ19_u.
Definition KS_vlJ19 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ19.regs0 PvlJ19.regs_out0).
Lemma KS_vlJ19_ok : BG.kept_ok 72 PvlJ19.regs0 PvlJ19.regs_out0 KS_vlJ19 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ19_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 18 -> getr R (reg 12) = Z_to_bv 64 19 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x37754 M')
        /\ (forall x, In x KS_vlJ19 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 227156
        /\ getr R' (reg 11) = Z_to_bv 64 147504).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ19.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ19.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ19.kn0).
  { unfold know_ok, PvlJ19.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ19.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ19.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ19.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ19.ps0) with 0x37754 in Hms. change (SR.ps_regs PvlJ19.ps0) with (map (fun i => (i, nth i PvlJ19.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ19.ps0) with PvlJ19.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ19.regs0 PvlJ19.regs_out0 72 KS_vlJ19 KS_vlJ19_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvlJ19.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ19.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvlJ19.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvlJ19.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ127 := LibSegBs_vlJ127_u.
Definition KS_vlJ127 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ127.regs0 PvlJ127.regs_out0).
Lemma KS_vlJ127_ok : BG.kept_ok 72 PvlJ127.regs0 PvlJ127.regs_out0 KS_vlJ127 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ127_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 126 -> getr R (reg 12) = Z_to_bv 64 127 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x376bc M')
        /\ (forall x, In x KS_vlJ127 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 127).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ127.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ127.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ127.kn0).
  { unfold know_ok, PvlJ127.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ127.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ127.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ127.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ127.ps0) with 0x376bc in Hms. change (SR.ps_regs PvlJ127.ps0) with (map (fun i => (i, nth i PvlJ127.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ127.ps0) with PvlJ127.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ127.regs0 PvlJ127.regs_out0 72 KS_vlJ127 KS_vlJ127_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PvlJ127.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ127.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJ255 := LibSegBs_vlJ255_u.
Definition KS_vlJ255 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJ255.regs0 PvlJ255.regs_out0).
Lemma KS_vlJ255_ok : BG.kept_ok 72 PvlJ255.regs0 PvlJ255.regs_out0 KS_vlJ255 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJ255_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 254 -> getr R (reg 12) = Z_to_bv 64 255 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x376bc M')
        /\ (forall x, In x KS_vlJ255 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 255).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJ255.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJ255.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJ255.kn0).
  { unfold know_ok, PvlJ255.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJ255.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJ255.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJ255.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJ255.ps0) with 0x376bc in Hms. change (SR.ps_regs PvlJ255.ps0) with (map (fun i => (i, nth i PvlJ255.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJ255.ps0) with PvlJ255.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJ255.regs0 PvlJ255.regs_out0 72 KS_vlJ255 KS_vlJ255_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PvlJ255.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJ255.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJz := LibSegBs_vlJz_u.
Definition KS_vlJz : list nat := Eval vm_compute in (BG.kept_list 72 PvlJz.regs0 PvlJz.regs_out0).
Lemma KS_vlJz_ok : BG.kept_ok 72 PvlJz.regs0 PvlJz.regs_out0 KS_vlJz = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJz_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 18446744073709551615 -> getr R (reg 12) = Z_to_bv 64 0 -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x376f4 M')
        /\ (forall x, In x KS_vlJz -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 255).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G11 G12 G13 G18 pvzI5 K1 K2 K3.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJz.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJz.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJz.kn0).
  { unfold know_ok, PvlJz.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJz.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJz.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJz.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJz.ps0) with 0x376f4 in Hms. change (SR.ps_regs PvlJz.ps0) with (map (fun i => (i, nth i PvlJz.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJz.ps0) with PvlJz.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJz.regs0 PvlJz.regs_out0 72 KS_vlJz KS_vlJz_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PvlJz.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJz.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJr1 := LibSegBs_vlJr1_u.
Definition KS_vlJr1 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJr1.regs0 PvlJr1.regs_out0).
Lemma KS_vlJr1_ok : BG.kept_ok 72 PvlJr1.regs0 PvlJr1.regs_out0 KS_vlJr1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJr1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 35%nat) - 1) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  20 <= (V 35%nat) <= 126 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x376f4 M')
        /\ (forall x, In x KS_vlJr1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 255).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G11 G12 G13 G18 pvzI6 K1 K2 K3 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJr1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJr1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJr1.kn0).
  { unfold know_ok, PvlJr1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJr1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJr1.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJr1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJr1.ps0) with 0x376f4 in Hms. change (SR.ps_regs PvlJr1.ps0) with (map (fun i => (i, nth i PvlJr1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJr1.ps0) with PvlJr1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJr1.regs0 PvlJr1.regs_out0 72 KS_vlJr1 KS_vlJr1_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PvlJr1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJr1.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvlJr2 := LibSegBs_vlJr2_u.
Definition KS_vlJr2 : list nat := Eval vm_compute in (BG.kept_list 72 PvlJr2.regs0 PvlJr2.regs_out0).
Lemma KS_vlJr2_ok : BG.kept_ok 72 PvlJr2.regs0 PvlJr2.regs_out0 KS_vlJr2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vlJr2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 35%nat) - 1) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 18 -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) ->
  140735332483248 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 176) 176 -> L5.img_clear M 65536 754672 ->
  128 <= (V 35%nat) <= 254 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3761c M) (st fx' R' 0x376f4 M')
        /\ (forall x, In x KS_vlJr2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 255).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G11 G12 G13 G18 pvzI6 K1 K2 K3 pvzI7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K0l; move K0l before pvzI6; pose proof (proj2 pvzI6) as K0r; move K0r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K4l; move K4l before pvzI7; pose proof (proj2 pvzI7) as K4r; move K4r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 37%nat. }
  assert (HR: regs_ok E PvlJr2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvlJr2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvlJr2.kn0).
  { unfold know_ok, PvlJr2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K4l K4r) | exact (conj K4l K4r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PvlJr2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PvlJr2.NX0 with 72%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvlJr2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvlJr2.ps0) with 0x376f4 in Hms. change (SR.ps_regs PvlJr2.ps0) with (map (fun i => (i, nth i PvlJr2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvlJr2.ps0) with PvlJr2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvlJr2.regs0 PvlJr2.regs_out0 72 KS_vlJr2 KS_vlJr2_ok HR Hag Hregs j Hj). }
  rewrite (BG.out_reg PvlJr2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvlJr2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End PNSRVEP.
