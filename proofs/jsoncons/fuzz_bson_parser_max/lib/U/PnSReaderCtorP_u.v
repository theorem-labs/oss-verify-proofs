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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_brcA_u LibSegBs_brcB_u LibSegBs_brcC_u LibSegBs_brcD_u LibSegBs_brcE_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSRCP.
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
Module PbrcA := LibSegBs_brcA_u.
Definition KS_brcA : list nat := Eval vm_compute in (BG.kept_list 52 PbrcA.regs0 PbrcA.regs_out0).
Lemma KS_brcA_ok : BG.kept_ok 52 PbrcA.regs0 PbrcA.regs_out0 KS_brcA = true. Proof. vm_compute. reflexivity. Qed.
Lemma brcA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 ((V 33%nat) + 432) -> getr R (reg 12) = Z_to_bv 64 (V 34%nat) ->
  140735332483232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 140735332483232 <= (V 33%nat) <= 140737488354624 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 704 <= ((V 2%nat) - 160)) -> L5.writable RSEGS M (V 33%nat) 416 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 16) -> ~ (((V 33%nat) + 24) <= bv_unsigned a < ((V 33%nat) + 24) + 16) -> ~ (((V 33%nat) + 104) <= bv_unsigned a < ((V 33%nat) + 104) + 136) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 160) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 16) -> ~ (((V 33%nat) + 24) <= i < ((V 33%nat) + 24) + 16) -> ~ (((V 33%nat) + 104) <= i < ((V 33%nat) + 104) + 136) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36410 M) (st fx' R' 0x81bdc M')
        /\ (forall x, In x KS_brcA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 222804
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 104)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 152)
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 432)
        /\ L5KA.zeros_at M' ((V 33%nat) + 160) 80
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 136) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 128) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 120) 6
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 112) 4098
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 144) ((V 33%nat) + 40)
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 140) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 32) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 24) 726984
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 152) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 104) 727024
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 222616
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 222304
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 12) 0
        /\ L5.u8_at RSEGS M' ((V 33%nat) + 10) 0
        /\ (L5.u8_at RSEGS M' ((V 33%nat) + 8) 1 /\ L5.u8_at RSEGS M' (((V 33%nat) + 8) + 1) 0)
        /\ L5.u64_at RSEGS M' (V 33%nat) 726752
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 G12 pvzI4 K1 K2 pvzI5 K4 K5 K6 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K0l; move K0l before pvzI4; pose proof (proj2 pvzI4) as K0r; move K0r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PbrcA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrcA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrcA.kn0).
  { unfold know_ok, PbrcA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrcA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrcA.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 160) <= bv_unsigned a < (vz_2 - 160) + 160) -> ~ ((vz_33 + 0) <= bv_unsigned a < (vz_33 + 0) + 16) -> ~ ((vz_33 + 24) <= bv_unsigned a < (vz_33 + 24) + 16) -> ~ ((vz_33 + 104) <= bv_unsigned a < (vz_33 + 104) + 136) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbrcA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrcA.ps0) with 0x81bdc in Hms. change (SR.ps_regs PbrcA.ps0) with (map (fun i => (i, nth i PbrcA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrcA.ps0) with PbrcA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrcA.regs0 PbrcA.regs_out0 52 KS_brcA KS_brcA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrcA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrcA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbrcA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbrcA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbrcA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrcA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbrcA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8x2_of_KWord2a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrcB := LibSegBs_brcB_u.
Definition KS_brcB : list nat := Eval vm_compute in (BG.kept_list 52 PbrcB.regs0 PbrcB.regs_out0).
Lemma KS_brcB_ok : BG.kept_ok 52 PbrcB.regs0 PbrcB.regs_out0 KS_brcB = true. Proof. vm_compute. reflexivity. Qed.
Lemma brcB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 104) ->
  140735332483232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 140735332483232 <= (V 33%nat) <= 140737488354624 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 704 <= ((V 2%nat) - 160)) -> L5.writable RSEGS M (V 33%nat) 416 -> L5.img_clear M 65536 754672 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 24) <= bv_unsigned a < ((V 33%nat) + 24) + 8) -> ~ (((V 33%nat) + 40) <= bv_unsigned a < ((V 33%nat) + 40) + 8) -> ~ (((V 33%nat) + 104) <= bv_unsigned a < ((V 33%nat) + 104) + 8) -> ~ (((V 33%nat) + 240) <= bv_unsigned a < ((V 33%nat) + 240) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 24) <= i < ((V 33%nat) + 24) + 8) -> ~ (((V 33%nat) + 40) <= i < ((V 33%nat) + 40) + 8) -> ~ (((V 33%nat) + 104) <= i < ((V 33%nat) + 104) + 8) -> ~ (((V 33%nat) + 240) <= i < ((V 33%nat) + 240) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36654 M) (st fx' R' 0x81bdc M')
        /\ (forall x, In x KS_brcB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 222864
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 48)
        /\ getr R' (reg 11) = Z_to_bv 64 740424
        /\ getr R' (reg 12) = Z_to_bv 64 726912
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 40) 740424
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 24) 726872
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 104) 726912
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 248) 18446744073709551615
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 240) 0).
Proof.
  intros pvzI1 pvzI2 G2 G8 G9 pvzI3 K1 K2 pvzI4 K4 K5 K6 K7.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 34%nat. }
  assert (HR: regs_ok E PbrcB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrcB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrcB.kn0).
  { unfold know_ok, PbrcB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K7]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrcB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrcB.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 24) <= bv_unsigned a < (vz_33 + 24) + 8) -> ~ ((vz_33 + 40) <= bv_unsigned a < (vz_33 + 40) + 8) -> ~ ((vz_33 + 104) <= bv_unsigned a < (vz_33 + 104) + 8) -> ~ ((vz_33 + 240) <= bv_unsigned a < (vz_33 + 240) + 12) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbrcB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrcB.ps0) with 0x81bdc in Hms. change (SR.ps_regs PbrcB.ps0) with (map (fun i => (i, nth i PbrcB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrcB.ps0) with PbrcB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrcB.regs0 PbrcB.regs_out0 52 KS_brcB KS_brcB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrcB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrcB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrcB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrcB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrcB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrcC := LibSegBs_brcC_u.
Definition KS_brcC : list nat := Eval vm_compute in (BG.kept_list 52 PbrcC.regs0 PbrcC.regs_out0).
Lemma KS_brcC_ok : BG.kept_ok 52 PbrcC.regs0 PbrcC.regs_out0 KS_brcC = true. Proof. vm_compute. reflexivity. Qed.
Lemma brcC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 104) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 432) ->
  140735332483232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 -> 140735332483232 <= (V 33%nat) <= 140737488354624 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 160) + 160 <= (V 33%nat) \/ (V 33%nat) + 704 <= ((V 2%nat) - 160)) -> L5.writable RSEGS M (V 33%nat) 416 -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) 222616 -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 24) -> L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 33%nat) + 432) 740792 ->
  L5.u64_at RSEGS M ((V 33%nat) + 592) ((V 33%nat) + 448) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 40) <= bv_unsigned a < ((V 33%nat) + 40) + 8) -> ~ (((V 33%nat) + 56) <= bv_unsigned a < ((V 33%nat) + 56) + 48) -> ~ (((V 33%nat) + 256) <= bv_unsigned a < ((V 33%nat) + 256) + 56) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 40) <= i < ((V 33%nat) + 40) + 8) -> ~ (((V 33%nat) + 56) <= i < ((V 33%nat) + 56) + 48) -> ~ (((V 33%nat) + 256) <= i < ((V 33%nat) + 256) + 56) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36690 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_brcC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 222680
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 16384
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 552)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 304) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 296) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 288) 16384
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 280) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 272) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 264) ((V 33%nat) + 448)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 256) ((V 33%nat) + 432)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 40) 727080
        /\ L5KA.zeros_at M' ((V 33%nat) + 56) 48).
Proof.
  intros pvzI1 pvzI2 G2 G8 G9 G18 pvzI3 K1 K2 pvzI4 K4 K5 K6 K7 K8 K9 K10 K11 K12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K0l; move K0l before pvzI3; pose proof (proj2 pvzI3) as K0r; move K0r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 34%nat. }
  assert (HR: regs_ok E PbrcC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrcC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrcC.kn0).
  { unfold know_ok, PbrcC.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K12]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrcC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrcC.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 40) <= bv_unsigned a < (vz_33 + 40) + 8) -> ~ ((vz_33 + 56) <= bv_unsigned a < (vz_33 + 56) + 48) -> ~ ((vz_33 + 256) <= bv_unsigned a < (vz_33 + 256) + 56) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbrcC.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrcC.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PbrcC.ps0) with (map (fun i => (i, nth i PbrcC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrcC.ps0) with PbrcC.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrcC.regs0 PbrcC.regs_out0 52 KS_brcC KS_brcC_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrcC.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrcC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcC.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbrcC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcC.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbrcC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcC.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrcC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcC.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrcC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcC.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbrcC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrcD := LibSegBs_brcD_u.
Definition KS_brcD : list nat := Eval vm_compute in (BG.kept_list 52 PbrcD.regs0 PbrcD.regs_out0).
Lemma KS_brcD_ok : BG.kept_ok 52 PbrcD.regs0 PbrcD.regs_out0 KS_brcD = true. Proof. vm_compute. reflexivity. Qed.
Lemma brcD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 9) = Z_to_bv 64 ((V 33%nat) + 16) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 552) ->
  140735332483232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 140735332483232 <= (V 33%nat) <= 140737488354624 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 33%nat) \/ (V 33%nat) + 704 <= ((V 2%nat) - 192)) -> L5.writable RSEGS M (V 33%nat) 416 -> 140735332483232 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 192)) -> ((V 34%nat) + 24 <= (V 33%nat) \/ (V 33%nat) + 704 <= (V 34%nat)) -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) 222304 -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 33%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 34%nat) ->
  L5.u64_at RSEGS M (V 34%nat) 726624 -> L5.u32_at RSEGS M ((V 34%nat) + 16) 1024 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 16) -> ~ (((V 2%nat) - 168) <= bv_unsigned a < ((V 2%nat) - 168) + 24) -> ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 68) -> ~ (((V 33%nat) + 280) <= bv_unsigned a < ((V 33%nat) + 280) + 8) -> ~ (((V 33%nat) + 296) <= bv_unsigned a < ((V 33%nat) + 296) + 8) -> ~ (((V 33%nat) + 312) <= bv_unsigned a < ((V 33%nat) + 312) + 4) -> ~ (((V 33%nat) + 320) <= bv_unsigned a < ((V 33%nat) + 320) + 96) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 16) -> ~ (((V 2%nat) - 168) <= i < ((V 2%nat) - 168) + 24) -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 68) -> ~ (((V 33%nat) + 280) <= i < ((V 33%nat) + 280) + 8) -> ~ (((V 33%nat) + 296) <= i < ((V 33%nat) + 296) + 8) -> ~ (((V 33%nat) + 312) <= i < ((V 33%nat) + 312) + 4) -> ~ (((V 33%nat) + 320) <= i < ((V 33%nat) + 320) + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x365d8 M) (st fx' R' 0xb03b8 M')
        /\ (forall x, In x KS_brcD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 223860
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 1
        /\ getr R' (reg 9) = Z_to_bv 64 0
        /\ getr R' (reg 10) = Z_to_bv 64 40
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 461168601842738791
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 60)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 56)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) ((V 2%nat) - 144)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 223340
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 2%nat) - 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) ((V 33%nat) + 392)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) 223148
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 33%nat) + 320)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 33%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 222412
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 64) 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 60) 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 56) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 408) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 400) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 392) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 384) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 376) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 368) 0
        /\ L5KA.zeros_at M' ((V 33%nat) + 320) 48
        /\ L5.u32_at RSEGS M' ((V 33%nat) + 312) 1024
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 296) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 280) (V 35%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G8 G9 G10 G18 pvzI5 K1 K2 pvzI6 K4 K5 K6 pvzI7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K7l; move K7l before pvzI7; pose proof (proj2 pvzI7) as K7r; move K7r before pvzI7; clear pvzI7.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PbrcD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrcD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrcD.kn0).
  { unfold know_ok, PbrcD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9; lia | clear - HV2l HV2r K0l K0r K5 K9; lia | clear - HV2l HV2r K0l K0r K5 K9; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K10; lia | clear - HV33l HV33r K3l K3r K5 K10; lia | clear - HV33l HV33r K3l K3r K5 K10; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9 K10) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9 K10) | clear; lia | exact K8]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9 K10) | evalEk ZA ltac:(clear) | generalize K9; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9 K10) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9; lia | clear - HV2l HV2r K0l K0r K5 K9; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | clear - HV2l HV2r K0l K0r K5 K9; lia | clear - HV2l HV2r K0l K0r K5 K9; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K10) | clear - HV2l HV2r K0l K0r K5 K9; lia | clear - HV2l HV2r K0l K0r K5 K9; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9 K10) | clear - HV2l HV2r K0l K0r K5 K9; lia | clear - HV2l HV2r K0l K0r K5 K9; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9 K10) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K7l K7r K9 K10; lia | clear - HV34l HV34r K7l K7r K9 K10; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV34l HV34r K7l K7r K9 K10) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K7l K7r K9 K10; lia | clear - HV34l HV34r K7l K7r K9 K10; lia | exactA K17]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrcD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrcD.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 16) -> ~ ((vz_2 - 168) <= bv_unsigned a < (vz_2 - 168) + 24) -> ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 68) -> ~ ((vz_33 + 280) <= bv_unsigned a < (vz_33 + 280) + 8) -> ~ ((vz_33 + 296) <= bv_unsigned a < (vz_33 + 296) + 8) -> ~ ((vz_33 + 312) <= bv_unsigned a < (vz_33 + 312) + 4) -> ~ ((vz_33 + 320) <= bv_unsigned a < (vz_33 + 320) + 96) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply Hfr. unfold PbrcD.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K9 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K10 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K10 Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K10 Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K10 Hn6; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrcD.ps0) with 0xb03b8 in Hms. change (SR.ps_regs PbrcD.ps0) with (map (fun i => (i, nth i PbrcD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrcD.ps0) with PbrcD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrcD.regs0 PbrcD.regs_out0 52 KS_brcD KS_brcD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrcD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrcD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcD.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbrcD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcD.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbrcD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcD.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbrcD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrcD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcD.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrcD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcD.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrcD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcD.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbrcD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcD.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbrcD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcD.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbrcD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcD.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbrcD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcD.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbrcD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcD.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbrcD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K9) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K10) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PbrcE := LibSegBs_brcE_u.
Definition KS_brcE : list nat := Eval vm_compute in (BG.kept_list 52 PbrcE.regs0 PbrcE.regs_out0).
Lemma KS_brcE_ok : BG.kept_ok 52 PbrcE.regs0 PbrcE.regs_out0 KS_brcE = true. Proof. vm_compute. reflexivity. Qed.
Lemma brcE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 1 -> getr R (reg 9) = Z_to_bv 64 0 -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 60) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 56) -> getr R (reg 20) = Z_to_bv 64 ((V 33%nat) + 392) ->
  140735332483232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 140735332483232 <= (V 33%nat) <= 140737488354624 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 192) + 192 <= (V 33%nat) \/ (V 33%nat) + 704 <= ((V 2%nat) - 192)) -> L5.writable RSEGS M (V 33%nat) 416 -> L5.img_clear M 65536 754672 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u32_at RSEGS M ((V 2%nat) - 56) 0 -> L5.u32_at RSEGS M ((V 2%nat) - 60) 0 ->
  L5.u32_at RSEGS M ((V 2%nat) - 64) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) 222412 -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 33%nat) + 16) ->
  L5.u64_at RSEGS M ((V 2%nat) - 96) ((V 33%nat) + 320) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 33%nat) + 392) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 152) 223148 ->
  L5.u64_at RSEGS M ((V 2%nat) - 160) ((V 33%nat) + 392) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 2%nat) - 64) -> L5.u64_at RSEGS M ((V 2%nat) - 184) 223340 -> L5.u64_at RSEGS M ((V 2%nat) - 192) ((V 2%nat) - 144) ->
  L5.u64_at RSEGS M ((V 33%nat) + 392) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 400) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 408) 0 -> 4096 <= (V 36%nat) <= 140737488355288 ->
  aligned (V 36%nat) 16 -> L5.writable RSEGS M (V 36%nat) 40 -> (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 40 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 40 <= (V 33%nat) \/ (V 33%nat) + 704 <= (V 36%nat)) ->
  ((V 36%nat) + 40 <= 65536 \/ 65536 + 689136 <= (V 36%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 176) <= bv_unsigned a < ((V 2%nat) - 176) + 64) -> ~ (((V 33%nat) + 392) <= bv_unsigned a < ((V 33%nat) + 392) + 24) -> ~ (((V 36%nat) + 0) <= bv_unsigned a < ((V 36%nat) + 0) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 176) <= i < ((V 2%nat) - 176) + 64) -> ~ (((V 33%nat) + 392) <= i < ((V 33%nat) + 392) + 24) -> ~ (((V 36%nat) + 0) <= i < ((V 36%nat) + 0) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x36a74 M) (st fx' R' 0x36504 M')
        /\ (forall x, In x KS_brcE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 40
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 17) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 400) ((V 36%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 408) ((V 36%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 392) (V 36%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 32) 0
        /\ L5.u8_at RSEGS M' ((V 36%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 16) 0
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 8) 0
        /\ L5.u32_at RSEGS M' (V 36%nat) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G18 G19 G20 pvzI10 K1 K2 pvzI11 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 pvzI12 K32 K33 K34 K35 K36.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV47l; move HV47l before pvzI8; pose proof (proj2 pvzI8) as HV47r; move HV47r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K0l; move K0l before pvzI10; pose proof (proj2 pvzI10) as K0r; move K0r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K31l; move K31l before pvzI12; pose proof (proj2 pvzI12) as K31r; move K31r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 49%nat. }
  assert (HR: regs_ok E PbrcE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbrcE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbrcE.kn0).
  { unfold know_ok, PbrcE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K35) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K35) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K35) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K35) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K35; lia | clear - HV33l HV33r K3l K3r K5 K35; lia | clear - HV33l HV33r K3l K3r K5 K35; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K35) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K35) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K35) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K35) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K35) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | clear - HV2l HV2r K0l K0r K5 K34; lia | clear - HV2l HV2r K0l K0r K5 K34; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K35) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K35; lia | clear - HV33l HV33r K3l K3r K5 K35; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K35) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K35; lia | clear - HV33l HV33r K3l K3r K5 K35; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K35) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K35; lia | clear - HV33l HV33r K3l K3r K5 K35; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K31l K31r K34 K35 K36) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K31l K31r K34 K35 K36) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K31l K31r K34 K35 K36) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K31l K31r K34 K35 K36; lia | clear - HV36l HV36r K31l K31r K34 K35 K36; lia | clear - HV36l HV36r K31l K31r K34 K35 K36; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K31l K31r K34 K35 K36) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K31l K31r K34 K35 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K31l K31r K34 K35 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbrcE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbrcE.NX0 with 52%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 176) <= bv_unsigned a < (vz_2 - 176) + 64) -> ~ ((vz_33 + 392) <= bv_unsigned a < (vz_33 + 392) + 24) -> ~ ((vz_36 + 0) <= bv_unsigned a < (vz_36 + 0) + 40) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbrcE.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K5 K34) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K5 K34 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K3l K3r K5 K35 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K31l K31r K34 K35 K36) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K31l K31r K34 K35 K36 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbrcE.ps0) with 0x36504 in Hms. change (SR.ps_regs PbrcE.ps0) with (map (fun i => (i, nth i PbrcE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbrcE.ps0) with PbrcE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbrcE.regs0 PbrcE.regs_out0 52 KS_brcE KS_brcE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbrcE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbrcE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbrcE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcE.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbrcE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcE.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbrcE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbrcE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcE.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbrcE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcE.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbrcE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcE.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbrcE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcE.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbrcE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcE.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbrcE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcE.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbrcE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcE.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PbrcE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcE.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbrcE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcE.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbrcE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbrcE.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbrcE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K35) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K31l K31r K34 K35 K36) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K35) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K31l K31r K34 K35 K36) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K3l K3r K5 K35) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K31l K31r K34 K35 K36) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K31l K31r K34 K35 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K31l K31r K34 K35 K36) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K31l K31r K34 K35 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K31l K31r K34 K35 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K31l K31r K34 K35 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End PNSRCP.
