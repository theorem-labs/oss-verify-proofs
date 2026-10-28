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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.seg Require LibSegBs_tvA_u LibSegBs_tvH1_u LibSegBs_tvH0_u LibSegBs_tvR_u LibSegBs_tvQ_u LibSegBs_tvE_u LibSegBs_tvF_u LibSegBs_tvD_u LibSegBs_tvD2_u LibSegBs_tvD3_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNSSVP.
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
Module PtvA := LibSegBs_tvA_u.
Definition KS_tvA_0 : list nat := Eval vm_compute in (BG.kept_list 60 PtvA.regs0 PtvA.regs_out0).
Lemma KS_tvA_0_ok : BG.kept_ok 60 PtvA.regs0 PtvA.regs_out0 KS_tvA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tvA_1 : list nat := Eval vm_compute in (BG.kept_list 60 PtvA.regs0 PtvA.regs_out1).
Lemma KS_tvA_1_ok : BG.kept_ok 60 PtvA.regs0 PtvA.regs_out1 KS_tvA_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tvA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 0 <= (V 35%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x3956c M) (st fx' R' 0x395a4 M')
        /\ (forall x, In x KS_tvA_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 35%nat)
        /\ 1 <= (((V 35%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0x3956c M) (st fx' R' 0x396a4 M')
        /\ (forall x, In x KS_tvA_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ (((V 35%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G10 G11 G12 pvzI5 K1 K2 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 36%nat. }
  assert (HR: regs_ok E PtvA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtvA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtvA.kn0).
  { unfold know_ok, PtvA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtvA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtvA.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 64) <= bv_unsigned a < (vz_2 - 64) + 64) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtvA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PtvA.ps0) with 0x395a4 in Hms. change (SR.ps_regs PtvA.ps0) with (map (fun i => (i, nth i PtvA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtvA.ps0) with PtvA.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvA.regs0 PtvA.regs_out0 60 KS_tvA_0 KS_tvA_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtvA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PtvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PtvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PtvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PtvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PtvA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  - right.
    change (SR.ps_pc PtvA.ps1) with 0x396a4 in Hms. change (SR.ps_regs PtvA.ps1) with (map (fun i => (i, nth i PtvA.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtvA.ps1) with PtvA.cells1 in Hcells. unfold PtvA.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvA.regs0 PtvA.regs_out1 60 KS_tvA_1 KS_tvA_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtvA.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PtvA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtvH1 := LibSegBs_tvH1_u.
Definition KS_tvH1_0 : list nat := Eval vm_compute in (BG.kept_list 60 PtvH1.regs0 PtvH1.regs_out0).
Lemma KS_tvH1_0_ok : BG.kept_ok 60 PtvH1.regs0 PtvH1.regs_out0 KS_tvH1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tvH1_1 : list nat := Eval vm_compute in (BG.kept_list 60 PtvH1.regs0 PtvH1.regs_out1).
Lemma KS_tvH1_1_ok : BG.kept_ok 60 PtvH1.regs0 PtvH1.regs_out1 KS_tvH1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tvH1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 33%nat) <= 140737488355032 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 33%nat) \/ (V 33%nat) + 296 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M ((V 33%nat) + 288) (V 37%nat) -> 1 <= (V 37%nat) <= 16384 ->
  L5.u64_at RSEGS M ((V 33%nat) + 272) 16384 -> 1 <= (V 36%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x395a4 M) (st fx' R' 0x395d0 M')
        /\ (forall x, In x KS_tvH1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234924
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ (V 36%nat) < 16384)
      \/ (msteps RSEGS (st fx R 0x395a4 M) (st fx' R' 0x395d0 M')
        /\ (forall x, In x KS_tvH1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234924
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 16384
        /\ 16384 <= (V 36%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G18 G21 pvzI7 K1 K2 pvzI8 K4 K5 K6 pvzI9 K8 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K7l; move K7l before pvzI9; pose proof (proj2 pvzI9) as K7r; move K7r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K9l; move K9l before pvzI10; pose proof (proj2 pvzI10) as K9r; move K9r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PtvH1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtvH1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtvH1.kn0).
  { unfold know_ok, PtvH1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K3l K3r K5) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K3l K3r K5; lia | clear - HV33l HV33r K3l K3r K5; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtvH1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtvH1.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtvH1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PtvH1.ps0) with 0x395d0 in Hms. change (SR.ps_regs PtvH1.ps0) with (map (fun i => (i, nth i PtvH1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtvH1.ps0) with PtvH1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvH1.regs0 PtvH1.regs_out0 60 KS_tvH1_0 KS_tvH1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtvH1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtvH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtvH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtvH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PtvH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PtvH1.ps1) with 0x395d0 in Hms. change (SR.ps_regs PtvH1.ps1) with (map (fun i => (i, nth i PtvH1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtvH1.ps1) with PtvH1.cells1 in Hcells. unfold PtvH1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvH1.regs0 PtvH1.regs_out1 60 KS_tvH1_1 KS_tvH1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtvH1.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PtvH1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH1.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PtvH1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PtvH1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH1.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PtvH1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtvH0 := LibSegBs_tvH0_u.
Definition KS_tvH0_0 : list nat := Eval vm_compute in (BG.kept_list 60 PtvH0.regs0 PtvH0.regs_out0).
Lemma KS_tvH0_0_ok : BG.kept_ok 60 PtvH0.regs0 PtvH0.regs_out0 KS_tvH0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tvH0_1 : list nat := Eval vm_compute in (BG.kept_list 60 PtvH0.regs0 PtvH0.regs_out1).
Lemma KS_tvH0_1_ok : BG.kept_ok 60 PtvH0.regs0 PtvH0.regs_out1 KS_tvH0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tvH0_2 : list nat := Eval vm_compute in (BG.kept_list 60 PtvH0.regs0 PtvH0.regs_out2).
Lemma KS_tvH0_2_ok : BG.kept_ok 60 PtvH0.regs0 PtvH0.regs_out2 KS_tvH0_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tvH0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> 140735332483072 <= (V 33%nat) <= 140737488355032 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 33%nat) \/ (V 33%nat) + 296 <= ((V 2%nat) - 64)) -> L5.img_clear M 65536 754672 -> L5.u64_at RSEGS M ((V 33%nat) + 288) 0 ->
  L5.u64_at RSEGS M ((V 33%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 33%nat) + 240) (V 38%nat) -> 140735332483072 <= (V 38%nat) <= 140737488355056 -> aligned (V 38%nat) 8 ->
  (((V 2%nat) - 64) + 64 <= (V 38%nat) \/ (V 38%nat) + 272 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M (V 38%nat) 740792 -> L5.u8_at RSEGS M ((V 38%nat) + 152) (V 52%nat) -> 0 <= (V 52%nat) <= 2 ->
  1 <= (V 36%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x395a4 M) (st fx' R' 0x395d0 M')
        /\ (forall x, In x KS_tvH0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234924
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ (V 36%nat) < 16384
        /\ (((((4611686018427387904 * (V 52%nat)) mod 2 ^ 64) / 9223372036854775808) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x395a4 M) (st fx' R' 0x3961c M')
        /\ (forall x, In x KS_tvH0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234924
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 19) = Z_to_bv 64 16384
        /\ 16384 <= (V 36%nat)
        /\ (((((4611686018427387904 * (V 52%nat)) mod 2 ^ 64) / 9223372036854775808) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x395a4 M) (st fx' R' 0x396a4 M')
        /\ (forall x, In x KS_tvH0_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 35%nat) - (V 36%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ 1 <= (((((4611686018427387904 * (V 52%nat)) mod 2 ^ 64) / 9223372036854775808) - 0) mod 2 ^ 64))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G18 G21 pvzI16 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 pvzI17 K12 K13 K14 K15 K16 K17 pvzI18 K19 K20 K21 K22 pvzI19 pvzI20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV49l; move HV49l before pvzI12; pose proof (proj2 pvzI12) as HV49r; move HV49r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV50l; move HV50l before pvzI13; pose proof (proj2 pvzI13) as HV50r; move HV50r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV51l; move HV51l before pvzI14; pose proof (proj2 pvzI14) as HV51r; move HV51r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV52l; move HV52l before pvzI15; pose proof (proj2 pvzI15) as HV52r; move HV52r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K11l; move K11l before pvzI17; pose proof (proj2 pvzI17) as K11r; move K11r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K18l; move K18l before pvzI18; pose proof (proj2 pvzI18) as K18r; move K18r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K23l; move K23l before pvzI19; pose proof (proj2 pvzI19) as K23r; move K23r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K24l; move K24l before pvzI20; pose proof (proj2 pvzI20) as K24r; move K24r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 38%nat => Z_to_bv 64 vz_38 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 38%nat => vz_38 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E PtvH0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtvH0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtvH0.kn0).
  { unfold know_ok, PtvH0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K13 K20; lia | clear - HV2l HV2r K0l K0r K13 K20; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K20) | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K20) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K20) | clear; lia | exact K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K20) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K20) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K18l K18r K20; lia | clear - HV38l HV38r K18l K18r K20; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV38l HV38r K18l K18r K20) | evalEk ZA ltac:(clear - HV52l HV52r K23l K23r) | clear - HV38l HV38r K18l K18r K20; lia | clear - HV38l HV38r K18l K18r K20; lia | byte_tac ltac:(clear - HV52l HV52r K23l K23r) | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtvH0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtvH0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtvH0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PtvH0.ps0) with 0x395d0 in Hms. change (SR.ps_regs PtvH0.ps0) with (map (fun i => (i, nth i PtvH0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtvH0.ps0) with PtvH0.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvH0.regs0 PtvH0.regs_out0 60 KS_tvH0_0 KS_tvH0_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtvH0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PtvH0.ps1) with 0x3961c in Hms. change (SR.ps_regs PtvH0.ps1) with (map (fun i => (i, nth i PtvH0.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtvH0.ps1) with PtvH0.cells1 in Hcells. unfold PtvH0.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvH0.regs0 PtvH0.regs_out1 60 KS_tvH0_1 KS_tvH0_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtvH0.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. 
    change (SR.ps_pc PtvH0.ps2) with 0x396a4 in Hms. change (SR.ps_regs PtvH0.ps2) with (map (fun i => (i, nth i PtvH0.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtvH0.ps2) with PtvH0.cells2 in Hcells. unfold PtvH0.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvH0.regs0 PtvH0.regs_out2 60 KS_tvH0_2 KS_tvH0_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtvH0.regs_out2 E' R' 1 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out2 E' R' 2 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out2 E' R' 8 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out2 E' R' 9 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out2 E' R' 19 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out2 E' R' 20 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvH0.regs_out2 E' R' 22 Hregs) by (clear; lia). cbn [nth PtvH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtvR := LibSegBs_tvR_u.
Definition KS_tvR : list nat := Eval vm_compute in (BG.kept_list 60 PtvR.regs0 PtvR.regs_out0).
Lemma KS_tvR_ok : BG.kept_ok 60 PtvR.regs0 PtvR.regs_out0 KS_tvR = true. Proof. vm_compute. reflexivity. Qed.
Lemma tvR_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 42%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M (V 34%nat) (V 39%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 8) ((V 39%nat) + (V 40%nat)) ->
  0 <= (V 39%nat) <= 140737488355328 -> 0 <= (V 40%nat) <= 134217728 -> 1 <= (V 42%nat) <= 16384 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x395d0 M) (st fx' R' 0x396ac M')
        /\ (forall x, In x KS_tvR -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 234984
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + (V 42%nat))
        /\ getr R' (reg 22) = Z_to_bv 64 (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G18 G19 G21 pvzI9 K1 K2 pvzI10 K4 K5 K6 K7 pvzI11 pvzI12 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV42l; move HV42l before pvzI8; pose proof (proj2 pvzI8) as HV42r; move HV42r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K0l; move K0l before pvzI9; pose proof (proj2 pvzI9) as K0r; move K0r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K8l; move K8l before pvzI11; pose proof (proj2 pvzI11) as K8r; move K8r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K9l; move K9l before pvzI12; pose proof (proj2 pvzI12) as K9r; move K9r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K10l; move K10l before pvzI13; pose proof (proj2 pvzI13) as K10r; move K10r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 39%nat => vz_39 | 40%nat => vz_40 | 42%nat => vz_42 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 43%nat. }
  assert (HR: regs_ok E PtvR.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtvR.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtvR.kn0).
  { unfold know_ok, PtvR.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV39l HV39r K8l K8r) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV39l HV39r K8l K8r HV40l HV40r K9l K9r) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtvR.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtvR.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtvR.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtvR.ps0) with 0x396ac in Hms. change (SR.ps_regs PtvR.ps0) with (map (fun i => (i, nth i PtvR.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtvR.ps0) with PtvR.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvR.regs0 PtvR.regs_out0 60 KS_tvR KS_tvR_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtvR.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtvR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtvR.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtvR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtvR.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtvR.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtvR.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PtvR.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtvQ := LibSegBs_tvQ_u.
Definition KS_tvQ : list nat := Eval vm_compute in (BG.kept_list 60 PtvQ.regs0 PtvQ.regs_out0).
Lemma KS_tvQ_ok : BG.kept_ok 60 PtvQ.regs0 PtvQ.regs_out0 KS_tvQ = true. Proof. vm_compute. reflexivity. Qed.
Lemma tvQ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 42%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 43%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M (V 34%nat) (V 39%nat) -> 4096 <= (V 39%nat) <= 140737488355328 ->
  1 <= (V 42%nat) <= 16384 -> 0 <= (V 43%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x395e8 M) (st fx' R' 0x370d0 M')
        /\ (forall x, In x KS_tvQ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 235016
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 39%nat) + (V 43%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 42%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 G2 G8 G9 G18 G19 G21 G22 pvzI9 K1 K2 pvzI10 K4 K5 K6 pvzI11 pvzI12 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV42l; move HV42l before pvzI7; pose proof (proj2 pvzI7) as HV42r; move HV42r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K0l; move K0l before pvzI9; pose proof (proj2 pvzI9) as K0r; move K0r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K7l; move K7l before pvzI11; pose proof (proj2 pvzI11) as K7r; move K7r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K8l; move K8l before pvzI12; pose proof (proj2 pvzI12) as K8r; move K8r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K9l; move K9l before pvzI13; pose proof (proj2 pvzI13) as K9r; move K9r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 39%nat => Z_to_bv 64 vz_39 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 39%nat => vz_39 | 42%nat => vz_42 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PtvQ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtvQ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtvQ.kn0).
  { unfold know_ok, PtvQ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtvQ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtvQ.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtvQ.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtvQ.ps0) with 0x370d0 in Hms. change (SR.ps_regs PtvQ.ps0) with (map (fun i => (i, nth i PtvQ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtvQ.ps0) with PtvQ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvQ.regs0 PtvQ.regs_out0 60 KS_tvQ KS_tvQ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtvQ.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtvQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtvQ.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtvQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtvQ.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtvQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtvQ.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtvQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtvE := LibSegBs_tvE_u.
Definition KS_tvE_0 : list nat := Eval vm_compute in (BG.kept_list 60 PtvE.regs0 PtvE.regs_out0).
Lemma KS_tvE_0_ok : BG.kept_ok 60 PtvE.regs0 PtvE.regs_out0 KS_tvE_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tvE_1 : list nat := Eval vm_compute in (BG.kept_list 60 PtvE.regs0 PtvE.regs_out1).
Lemma KS_tvE_1_ok : BG.kept_ok 60 PtvE.regs0 PtvE.regs_out1 KS_tvE_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tvE_2 : list nat := Eval vm_compute in (BG.kept_list 60 PtvE.regs0 PtvE.regs_out2).
Lemma KS_tvE_2_ok : BG.kept_ok 60 PtvE.regs0 PtvE.regs_out2 KS_tvE_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tvE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 53%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 (V 42%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 43%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> 0 <= (V 53%nat) <= 16384 ->
  1 <= (V 42%nat) <= 16384 -> 0 <= (V 43%nat) <= 134217728 -> 1 <= (V 36%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x39608 M) (st fx' R' 0x396ac M')
        /\ (forall x, In x KS_tvE_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 235124
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 43%nat) + (V 53%nat))
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ 1 <= (((V 53%nat) - (V 42%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x39608 M) (st fx' R' 0x395a4 M')
        /\ (forall x, In x KS_tvE_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) - (V 53%nat))
        /\ 1 <= (((((V 36%nat) + ((18446744073709551615 * (V 53%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64)
        /\ (((V 53%nat) - (V 42%nat)) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x39608 M) (st fx' R' 0x396a4 M')
        /\ (forall x, In x KS_tvE_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 35%nat) + (((-1) * (V 36%nat)) + (V 53%nat)))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ (((((V 36%nat) + ((18446744073709551615 * (V 53%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ (((V 53%nat) - (V 42%nat)) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G8 G9 G10 G18 G19 G21 G22 pvzI17 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 pvzI18 pvzI19 pvzI20 pvzI21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV44l; move HV44l before pvzI8; pose proof (proj2 pvzI8) as HV44r; move HV44r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV45l; move HV45l before pvzI9; pose proof (proj2 pvzI9) as HV45r; move HV45r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV46l; move HV46l before pvzI10; pose proof (proj2 pvzI10) as HV46r; move HV46r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV47l; move HV47l before pvzI11; pose proof (proj2 pvzI11) as HV47r; move HV47r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV48l; move HV48l before pvzI12; pose proof (proj2 pvzI12) as HV48r; move HV48r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV49l; move HV49l before pvzI13; pose proof (proj2 pvzI13) as HV49r; move HV49r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV50l; move HV50l before pvzI14; pose proof (proj2 pvzI14) as HV50r; move HV50r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV51l; move HV51l before pvzI15; pose proof (proj2 pvzI15) as HV51r; move HV51r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV53l; move HV53l before pvzI16; pose proof (proj2 pvzI16) as HV53r; move HV53r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K0l; move K0l before pvzI17; pose proof (proj2 pvzI17) as K0r; move K0r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K11l; move K11l before pvzI18; pose proof (proj2 pvzI18) as K11r; move K11r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K12l; move K12l before pvzI19; pose proof (proj2 pvzI19) as K12r; move K12r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K13l; move K13l before pvzI20; pose proof (proj2 pvzI20) as K13r; move K13r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K14l; move K14l before pvzI21; pose proof (proj2 pvzI21) as K14r; move K14r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PtvE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtvE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtvE.kn0).
  { unfold know_ok, PtvE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtvE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtvE.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtvE.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PtvE.ps0) with 0x396ac in Hms. change (SR.ps_regs PtvE.ps0) with (map (fun i => (i, nth i PtvE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtvE.ps0) with PtvE.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvE.regs0 PtvE.regs_out0 60 KS_tvE_0 KS_tvE_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtvE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtvE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtvE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvE.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtvE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvE.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PtvE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PtvE.ps1) with 0x395a4 in Hms. change (SR.ps_regs PtvE.ps1) with (map (fun i => (i, nth i PtvE.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtvE.ps1) with PtvE.cells1 in Hcells. unfold PtvE.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvE.regs0 PtvE.regs_out1 60 KS_tvE_1 KS_tvE_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtvE.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth PtvE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvE.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PtvE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. 
    change (SR.ps_pc PtvE.ps2) with 0x396a4 in Hms. change (SR.ps_regs PtvE.ps2) with (map (fun i => (i, nth i PtvE.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtvE.ps2) with PtvE.cells2 in Hcells. unfold PtvE.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvE.regs0 PtvE.regs_out2 60 KS_tvE_2 KS_tvE_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtvE.regs_out2 E' R' 1 Hregs) by (clear; lia). cbn [nth PtvE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvE.regs_out2 E' R' 2 Hregs) by (clear; lia). cbn [nth PtvE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvE.regs_out2 E' R' 8 Hregs) by (clear; lia). cbn [nth PtvE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvE.regs_out2 E' R' 9 Hregs) by (clear; lia). cbn [nth PtvE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvE.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PtvE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvE.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth PtvE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvE.regs_out2 E' R' 19 Hregs) by (clear; lia). cbn [nth PtvE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvE.regs_out2 E' R' 20 Hregs) by (clear; lia). cbn [nth PtvE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvE.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth PtvE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvE.regs_out2 E' R' 22 Hregs) by (clear; lia). cbn [nth PtvE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtvF := LibSegBs_tvF_u.
Definition KS_tvF_0 : list nat := Eval vm_compute in (BG.kept_list 60 PtvF.regs0 PtvF.regs_out0).
Lemma KS_tvF_0_ok : BG.kept_ok 60 PtvF.regs0 PtvF.regs_out0 KS_tvF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tvF_1 : list nat := Eval vm_compute in (BG.kept_list 60 PtvF.regs0 PtvF.regs_out1).
Lemma KS_tvF_1_ok : BG.kept_ok 60 PtvF.regs0 PtvF.regs_out1 KS_tvF_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tvF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 20) = Z_to_bv 64 (V 42%nat) -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> 0 <= (V 42%nat) <= 16384 ->
  1 <= (V 36%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x39674 M) (st fx' R' 0x395a4 M')
        /\ (forall x, In x KS_tvF_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) - (V 42%nat))
        /\ 1 <= (((((V 36%nat) + ((18446744073709551615 * (V 42%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x39674 M) (st fx' R' 0x396a4 M')
        /\ (forall x, In x KS_tvF_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 35%nat) + (((-1) * (V 36%nat)) + (V 42%nat)))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ (((((V 36%nat) + ((18446744073709551615 * (V 42%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 G2 G8 G9 G18 G20 G21 pvzI15 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV42l; move HV42l before pvzI6; pose proof (proj2 pvzI6) as HV42r; move HV42r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV49l; move HV49l before pvzI12; pose proof (proj2 pvzI12) as HV49r; move HV49r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV50l; move HV50l before pvzI13; pose proof (proj2 pvzI13) as HV50r; move HV50r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV51l; move HV51l before pvzI14; pose proof (proj2 pvzI14) as HV51r; move HV51r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K0l; move K0l before pvzI15; pose proof (proj2 pvzI15) as K0r; move K0r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K11l; move K11l before pvzI16; pose proof (proj2 pvzI16) as K11r; move K11r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K12l; move K12l before pvzI17; pose proof (proj2 pvzI17) as K12r; move K12r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 42%nat => Z_to_bv 64 vz_42 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 42%nat => vz_42 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PtvF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtvF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtvF.kn0).
  { unfold know_ok, PtvF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K11l K11r) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtvF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtvF.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtvF.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc PtvF.ps0) with 0x395a4 in Hms. change (SR.ps_regs PtvF.ps0) with (map (fun i => (i, nth i PtvF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtvF.ps0) with PtvF.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvF.regs0 PtvF.regs_out0 60 KS_tvF_0 KS_tvF_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtvF.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PtvF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc PtvF.ps1) with 0x396a4 in Hms. change (SR.ps_regs PtvF.ps1) with (map (fun i => (i, nth i PtvF.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtvF.ps1) with PtvF.cells1 in Hcells. unfold PtvF.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvF.regs0 PtvF.regs_out1 60 KS_tvF_1 KS_tvF_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtvF.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PtvF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvF.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PtvF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvF.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PtvF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvF.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PtvF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvF.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PtvF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvF.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PtvF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvF.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PtvF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvF.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth PtvF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvF.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PtvF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvF.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth PtvF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtvD := LibSegBs_tvD_u.
Definition KS_tvD : list nat := Eval vm_compute in (BG.kept_list 60 PtvD.regs0 PtvD.regs_out0).
Lemma KS_tvD_ok : BG.kept_ok 60 PtvD.regs0 PtvD.regs_out0 KS_tvD = true. Proof. vm_compute. reflexivity. Qed.
Lemma tvD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 16384 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M (V 34%nat) (V 39%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 8) ((V 39%nat) + (V 40%nat)) ->
  0 <= (V 39%nat) <= 140737488355328 -> 0 <= (V 40%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x3961c M) (st fx' R' 0x396ac M')
        /\ (forall x, In x KS_tvD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 235060
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 16384)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 40%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G18 G19 G21 pvzI8 K1 K2 pvzI9 K4 K5 K6 K7 pvzI10 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV40l; move HV40l before pvzI7; pose proof (proj2 pvzI7) as HV40r; move HV40r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K8l; move K8l before pvzI10; pose proof (proj2 pvzI10) as K8r; move K8r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K9l; move K9l before pvzI11; pose proof (proj2 pvzI11) as K9r; move K9r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 39%nat => vz_39 | 40%nat => vz_40 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PtvD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtvD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtvD.kn0).
  { unfold know_ok, PtvD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV39l HV39r K8l K8r) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV39l HV39r K8l K8r HV40l HV40r K9l K9r) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtvD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtvD.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtvD.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtvD.ps0) with 0x396ac in Hms. change (SR.ps_regs PtvD.ps0) with (map (fun i => (i, nth i PtvD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtvD.ps0) with PtvD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvD.regs0 PtvD.regs_out0 60 KS_tvD KS_tvD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtvD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtvD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtvD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtvD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtvD.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtvD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtvD.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PtvD.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtvD2 := LibSegBs_tvD2_u.
Definition KS_tvD2 : list nat := Eval vm_compute in (BG.kept_list 60 PtvD2.regs0 PtvD2.regs_out0).
Lemma KS_tvD2_ok : BG.kept_ok 60 PtvD2.regs0 PtvD2.regs_out0 KS_tvD2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tvD2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 16384 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 43%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 140735332483072 <= (V 34%nat) <= 140737488355304 ->
  aligned (V 34%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 34%nat) \/ (V 34%nat) + 24 <= ((V 2%nat) - 64)) -> L5.u64_at RSEGS M (V 34%nat) (V 39%nat) -> 4096 <= (V 39%nat) <= 140737488355328 ->
  0 <= (V 43%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x39634 M) (st fx' R' 0x382d4 M')
        /\ (forall x, In x KS_tvD2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 235092
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 39%nat) + (V 43%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 16384).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G18 G19 G21 G22 pvzI8 K1 K2 pvzI9 K4 K5 K6 pvzI10 pvzI11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K0l; move K0l before pvzI8; pose proof (proj2 pvzI8) as K0r; move K0r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K3l; move K3l before pvzI9; pose proof (proj2 pvzI9) as K3r; move K3r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K8l; move K8l before pvzI11; pose proof (proj2 pvzI11) as K8r; move K8r before pvzI11; clear pvzI11.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 39%nat => Z_to_bv 64 vz_39 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 39%nat => vz_39 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PtvD2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtvD2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtvD2.kn0).
  { unfold know_ok, PtvD2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | clear - HV2l HV2r K0l K0r K5; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K5) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear) | generalize K5; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K3l K3r K5) | evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | clear - HV34l HV34r K3l K3r K5; lia | clear - HV34l HV34r K3l K3r K5; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtvD2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtvD2.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PtvD2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PtvD2.ps0) with 0x382d4 in Hms. change (SR.ps_regs PtvD2.ps0) with (map (fun i => (i, nth i PtvD2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PtvD2.ps0) with PtvD2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvD2.regs0 PtvD2.regs_out0 60 KS_tvD2 KS_tvD2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PtvD2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtvD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtvD2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtvD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PtvD2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtvD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PtvD2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PtvD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PtvD3 := LibSegBs_tvD3_u.
Definition KS_tvD3_0 : list nat := Eval vm_compute in (BG.kept_list 60 PtvD3.regs0 PtvD3.regs_out0).
Lemma KS_tvD3_0_ok : BG.kept_ok 60 PtvD3.regs0 PtvD3.regs_out0 KS_tvD3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tvD3_1 : list nat := Eval vm_compute in (BG.kept_list 60 PtvD3.regs0 PtvD3.regs_out1).
Lemma KS_tvD3_1_ok : BG.kept_ok 60 PtvD3.regs0 PtvD3.regs_out1 KS_tvD3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_tvD3_2 : list nat := Eval vm_compute in (BG.kept_list 60 PtvD3.regs0 PtvD3.regs_out2).
Lemma KS_tvD3_2_ok : BG.kept_ok 60 PtvD3.regs0 PtvD3.regs_out2 KS_tvD3_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma tvD3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 35%nat) -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 10) = Z_to_bv 64 (V 53%nat) -> getr R (reg 18) = Z_to_bv 64 (V 33%nat) -> getr R (reg 19) = Z_to_bv 64 16384 -> getr R (reg 21) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 43%nat) ->
  140735332483136 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> 140735332483072 <= (V 33%nat) <= 140737488355032 ->
  aligned (V 33%nat) 8 -> (((V 2%nat) - 64) + 64 <= (V 33%nat) \/ (V 33%nat) + 296 <= ((V 2%nat) - 64)) -> L5.defined M ((V 33%nat) + 256) 8 -> L5.writable RSEGS M ((V 33%nat) + 256) 8 ->
  0 <= (V 53%nat) <= 16384 -> 0 <= (V 43%nat) <= 134217728 -> 16384 <= (V 36%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 256) <= bv_unsigned a < ((V 33%nat) + 256) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 256) <= i < ((V 33%nat) + 256) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0x39654 M) (st fx' R' 0x396ac M')
        /\ (forall x, In x KS_tvD3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 235124
        /\ getr R' (reg 10) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 43%nat) + (V 53%nat))
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ 1 <= (((V 53%nat) - 16384) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0x39654 M) (st fx' R' 0x395a4 M')
        /\ (forall x, In x KS_tvD3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) - (V 53%nat))
        /\ 1 <= (((((V 36%nat) + ((18446744073709551615 * (V 53%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64)
        /\ (((V 53%nat) - 16384) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0x39654 M) (st fx' R' 0x396a4 M')
        /\ (forall x, In x KS_tvD3_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 35%nat) + (((-1) * (V 36%nat)) + (V 53%nat)))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ (((((V 36%nat) + ((18446744073709551615 * (V 53%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ (((V 53%nat) - 16384) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G10 G18 G19 G21 G22 pvzI16 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 pvzI17 K12 K13 K14 K15 pvzI18 pvzI19 pvzI20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV49l; move HV49l before pvzI12; pose proof (proj2 pvzI12) as HV49r; move HV49r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV50l; move HV50l before pvzI13; pose proof (proj2 pvzI13) as HV50r; move HV50r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV51l; move HV51l before pvzI14; pose proof (proj2 pvzI14) as HV51r; move HV51r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV53l; move HV53l before pvzI15; pose proof (proj2 pvzI15) as HV53r; move HV53r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K0l; move K0l before pvzI16; pose proof (proj2 pvzI16) as K0r; move K0r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K11l; move K11l before pvzI17; pose proof (proj2 pvzI17) as K11r; move K11r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K16l; move K16l before pvzI18; pose proof (proj2 pvzI18) as K16r; move K16r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K17l; move K17l before pvzI19; pose proof (proj2 pvzI19) as K17r; move K17r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K18l; move K18l before pvzI20; pose proof (proj2 pvzI20) as K18r; move K18r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_53 := V 53%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 53%nat => Z_to_bv 64 vz_53 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 43%nat => vz_43 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 53%nat => vz_53 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PtvD3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PtvD3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PtvD3.kn0).
  { unfold know_ok, PtvD3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | clear - HV33l HV33r K11l K11r K13; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PtvD3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PtvD3.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_33 + 256) <= bv_unsigned a < (vz_33 + 256) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PtvD3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K11l K11r K13) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K11l K11r K13 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PtvD3.ps0) with 0x396ac in Hms. change (SR.ps_regs PtvD3.ps0) with (map (fun i => (i, nth i PtvD3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtvD3.ps0) with PtvD3.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvD3.regs0 PtvD3.regs_out0 60 KS_tvD3_0 KS_tvD3_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtvD3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvD3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvD3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvD3.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PtvD3.ps1) with 0x395a4 in Hms. change (SR.ps_regs PtvD3.ps1) with (map (fun i => (i, nth i PtvD3.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtvD3.ps1) with PtvD3.cells1 in Hcells. unfold PtvD3.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvD3.regs0 PtvD3.regs_out1 60 KS_tvD3_1 KS_tvD3_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtvD3.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvD3.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. 
    change (SR.ps_pc PtvD3.ps2) with 0x396a4 in Hms. change (SR.ps_regs PtvD3.ps2) with (map (fun i => (i, nth i PtvD3.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PtvD3.ps2) with PtvD3.cells2 in Hcells. unfold PtvD3.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PtvD3.regs0 PtvD3.regs_out2 60 KS_tvD3_2 KS_tvD3_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PtvD3.regs_out2 E' R' 1 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvD3.regs_out2 E' R' 2 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvD3.regs_out2 E' R' 8 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvD3.regs_out2 E' R' 9 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvD3.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvD3.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvD3.regs_out2 E' R' 19 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvD3.regs_out2 E' R' 20 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvD3.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PtvD3.regs_out2 E' R' 22 Hregs) by (clear; lia). cbn [nth PtvD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

End PNSSVP.
