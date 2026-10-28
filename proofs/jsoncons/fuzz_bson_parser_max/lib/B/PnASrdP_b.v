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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_srdA_b LibSegBa_srdH1_b LibSegBa_srdH0_b LibSegBa_srdRS_b LibSegBa_srdRL_b LibSegBa_srdQS_b LibSegBa_srdQL_b LibSegBa_srdE_b LibSegBa_srdF_b LibSegBa_srdDS_b LibSegBa_srdDL_b LibSegBa_srdD2_b LibSegBa_srdD3_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMASRDP.
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
Module PsrdA := LibSegBa_srdA_b.
Definition KS_srdA_0 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdA.regs0 PsrdA.regs_out0).
Lemma KS_srdA_0_ok : BG.kept_ok 70 PsrdA.regs0 PsrdA.regs_out0 KS_srdA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_srdA_1 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdA.regs0 PsrdA.regs_out1).
Lemma KS_srdA_1_ok : BG.kept_ok 70 PsrdA.regs0 PsrdA.regs_out1 KS_srdA_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma srdA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 (V 38%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> 6905856 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 192)) ->
  6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 ->
  L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) -> 0 <= (V 38%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb50e0 M) (st fx' R' 0xb51a0 M')
        /\ (forall x, In x KS_srdA_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((((V 37%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 ((((V 36%nat) + 256) / 8) + 2147450880)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 37%nat) + 8) / 8)
        /\ getr R' (reg 14) = Z_to_bv 64 ((((V 37%nat) + 16) / 8) + 2147450880)
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + 272)
        /\ getr R' (reg 20) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 37%nat) + 1)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) ((((V 37%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((((V 37%nat) + 16) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) ((((V 36%nat) + 256) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) ((V 37%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) ((V 37%nat) + 16)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 36%nat) + 256)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) 0
        /\ 1 <= (((V 38%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 38%nat)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0xb50e0 M) (st fx' R' 0xb53b8 M')
        /\ (forall x, In x KS_srdA_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 38%nat)
        /\ (((V 38%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 38%nat)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G10 G11 G12 K0 K1 K2 pvzI5 K4 K5 pvzI6 K7 K8 K9 K10 K11 pvzI7 K13 K14 K15 K16 K17 K18 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K3l; move K3l before pvzI5; pose proof (proj2 pvzI5) as K3r; move K3r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K6l; move K6l before pvzI6; pose proof (proj2 pvzI6) as K6r; move K6r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K12l; move K12l before pvzI7; pose proof (proj2 pvzI7) as K12r; move K12r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K19l; move K19l before pvzI8; pose proof (proj2 pvzI8) as K19r; move K19r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PsrdA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrdA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrdA.kn0).
  { unfold know_ok, PsrdA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | clear - HV36l HV36r K6l K6r K8 K11 K18; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | clear - HV37l HV37r K12l K12r K14 K17 K18; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrdA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrdA.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 192) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PsrdA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PsrdA.ps0) with 0xb51a0 in Hms. change (SR.ps_regs PsrdA.ps0) with (map (fun i => (i, nth i PsrdA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PsrdA.ps0) with PsrdA.cells0 in Hcells. unfold PsrdA.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdA.regs0 PsrdA.regs_out0 70 KS_srdA_0 KS_srdA_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PsrdA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdA.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdA.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdA.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdA.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdA.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdA.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r K14 K17 K18) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r K8 K11 K18) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K19l K19r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. 
    change (SR.ps_pc PsrdA.ps1) with 0xb53b8 in Hms. change (SR.ps_regs PsrdA.ps1) with (map (fun i => (i, nth i PsrdA.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PsrdA.ps1) with PsrdA.cells1 in Hcells. unfold PsrdA.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdA.regs0 PsrdA.regs_out1 70 KS_srdA_1 KS_srdA_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PsrdA.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K19l K19r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrdH1 := LibSegBa_srdH1_b.
Definition KS_srdH1_0 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdH1.regs0 PsrdH1.regs_out0).
Lemma KS_srdH1_0_ok : BG.kept_ok 70 PsrdH1.regs0 PsrdH1.regs_out0 KS_srdH1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_srdH1_1 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdH1.regs0 PsrdH1.regs_out1).
Lemma KS_srdH1_1_ok : BG.kept_ok 70 PsrdH1.regs0 PsrdH1.regs_out1 KS_srdH1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma srdH1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 ((V 37%nat) + 1) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 37%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((((V 37%nat) + 16) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 37%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 36%nat) + 256) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 0 -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 192)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) -> 1 <= (V 33%nat) <= 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> 1 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb51a0 M) (st fx' R' 0xb51e4 M')
        /\ (forall x, In x KS_srdH1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 741800
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 2147450880
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 (V 39%nat)
        /\ (V 39%nat) < 16384
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 741800)
      \/ (msteps RSEGS (st fx R 0xb51a0 M) (st fx' R' 0xb51e4 M')
        /\ (forall x, In x KS_srdH1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 741800
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 2147450880
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 16384
        /\ 16384 <= (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 741800)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G18 G19 G20 G21 G23 G26 G27 K0 K1 K2 pvzI20 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 pvzI21 K28 K29 K30 K31 K32 pvzI22 K34 K35 K36 K37 K38 K39 K40 pvzI23 K42 pvzI24.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV39l; move HV39l before pvzI6; pose proof (proj2 pvzI6) as HV39r; move HV39r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV49l; move HV49l before pvzI8; pose proof (proj2 pvzI8) as HV49r; move HV49r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV52l; move HV52l before pvzI11; pose proof (proj2 pvzI11) as HV52r; move HV52r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV53l; move HV53l before pvzI12; pose proof (proj2 pvzI12) as HV53r; move HV53r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV54l; move HV54l before pvzI13; pose proof (proj2 pvzI13) as HV54r; move HV54r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV55l; move HV55l before pvzI14; pose proof (proj2 pvzI14) as HV55r; move HV55r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV56l; move HV56l before pvzI15; pose proof (proj2 pvzI15) as HV56r; move HV56r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV57l; move HV57l before pvzI16; pose proof (proj2 pvzI16) as HV57r; move HV57r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV58l; move HV58l before pvzI17; pose proof (proj2 pvzI17) as HV58r; move HV58r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV59l; move HV59l before pvzI18; pose proof (proj2 pvzI18) as HV59r; move HV59r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV60l; move HV60l before pvzI19; pose proof (proj2 pvzI19) as HV60r; move HV60r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K27l; move K27l before pvzI21; pose proof (proj2 pvzI21) as K27r; move K27r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K33l; move K33l before pvzI22; pose proof (proj2 pvzI22) as K33r; move K33r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K41l; move K41l before pvzI23; pose proof (proj2 pvzI23) as K41r; move K41r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K43l; move K43l before pvzI24; pose proof (proj2 pvzI24) as K43r; move K43r before pvzI24; clear pvzI24.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PsrdH1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrdH1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrdH1.kn0).
  { unfold know_ok, PsrdH1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear; lia | exact K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear - HV33l HV33r K41l K41r) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K43l K43r) | exact (conj K43l K43r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrdH1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrdH1.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PsrdH1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PsrdH1.ps0) with 0xb51e4 in Hms. change (SR.ps_regs PsrdH1.ps0) with (map (fun i => (i, nth i PsrdH1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PsrdH1.ps0) with PsrdH1.cells0 in Hcells. unfold PsrdH1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdH1.regs0 PsrdH1.regs_out0 70 KS_srdH1_0 KS_srdH1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PsrdH1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrdH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PsrdH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PsrdH1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. 
    change (SR.ps_pc PsrdH1.ps1) with 0xb51e4 in Hms. change (SR.ps_regs PsrdH1.ps1) with (map (fun i => (i, nth i PsrdH1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PsrdH1.ps1) with PsrdH1.cells1 in Hcells. unfold PsrdH1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdH1.regs0 PsrdH1.regs_out1 70 KS_srdH1_1 KS_srdH1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PsrdH1.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdH1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH1.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdH1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdH1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH1.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrdH1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH1.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PsrdH1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH1.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PsrdH1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrdH0 := LibSegBa_srdH0_b.
Definition KS_srdH0_0 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdH0.regs0 PsrdH0.regs_out0).
Lemma KS_srdH0_0_ok : BG.kept_ok 70 PsrdH0.regs0 PsrdH0.regs_out0 KS_srdH0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_srdH0_1 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdH0.regs0 PsrdH0.regs_out1).
Lemma KS_srdH0_1_ok : BG.kept_ok 70 PsrdH0.regs0 PsrdH0.regs_out1 KS_srdH0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_srdH0_2 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdH0.regs0 PsrdH0.regs_out2).
Lemma KS_srdH0_2_ok : BG.kept_ok 70 PsrdH0.regs0 PsrdH0.regs_out2 KS_srdH0_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma srdH0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 -> 0 <= (V 62%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 ((V 37%nat) + 1) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 37%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((((V 37%nat) + 16) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 37%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 36%nat) + 256) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 0 -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 192)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> 6905856 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 45%nat) \/ (V 45%nat) + 272 <= 2147446784) -> L5KA.zeros_at M (((V 45%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 45%nat) 272 -> (((V 2%nat) - 192) + 192 <= (V 45%nat) \/ (V 45%nat) + 272 <= ((V 2%nat) - 192)) ->
  ((V 36%nat) + 296 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) -> ((V 37%nat) + 24 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 37%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 240) (V 45%nat) -> L5.u64_at RSEGS M (V 45%nat) 1265968 ->
  L5.u8_at RSEGS M ((V 45%nat) + 152) (V 62%nat) -> 0 <= (V 62%nat) <= 2 -> L5KA.zeros_at M 2147609123 1 -> 1 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb51a0 M) (st fx' R' 0xb51e4 M')
        /\ (forall x, In x KS_srdH0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 741800
        /\ getr R' (reg 10) = Z_to_bv 64 16384
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 2147450880
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 (V 39%nat)
        /\ (V 39%nat) < 16384
        /\ (((((4611686018427387904 * (V 62%nat)) mod 2 ^ 64) / 9223372036854775808) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 741800)
      \/ (msteps RSEGS (st fx R 0xb51a0 M) (st fx' R' 0xb5280 M')
        /\ (forall x, In x KS_srdH0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 741800
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 2147450880
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 16384
        /\ 16384 <= (V 39%nat)
        /\ (((((4611686018427387904 * (V 62%nat)) mod 2 ^ 64) / 9223372036854775808) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 741800)
      \/ (msteps RSEGS (st fx R 0xb51a0 M) (st fx' R' 0xb53b8 M')
        /\ (forall x, In x KS_srdH0_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 38%nat) - (V 39%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 2147450880
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 60%nat)
        /\ 1 <= (((((4611686018427387904 * (V 62%nat)) mod 2 ^ 64) / 9223372036854775808) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) 741800)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 G2 G8 G9 G18 G19 G20 G21 G23 G26 G27 K0 K1 K2 pvzI21 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 pvzI22 K28 K29 K30 K31 K32 pvzI23 K34 K35 K36 K37 K38 K39 K40 K41 pvzI24 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 pvzI25 K54 pvzI26.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV49l; move HV49l before pvzI8; pose proof (proj2 pvzI8) as HV49r; move HV49r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV52l; move HV52l before pvzI11; pose proof (proj2 pvzI11) as HV52r; move HV52r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV53l; move HV53l before pvzI12; pose proof (proj2 pvzI12) as HV53r; move HV53r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV54l; move HV54l before pvzI13; pose proof (proj2 pvzI13) as HV54r; move HV54r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV55l; move HV55l before pvzI14; pose proof (proj2 pvzI14) as HV55r; move HV55r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV56l; move HV56l before pvzI15; pose proof (proj2 pvzI15) as HV56r; move HV56r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV57l; move HV57l before pvzI16; pose proof (proj2 pvzI16) as HV57r; move HV57r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV58l; move HV58l before pvzI17; pose proof (proj2 pvzI17) as HV58r; move HV58r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV59l; move HV59l before pvzI18; pose proof (proj2 pvzI18) as HV59r; move HV59r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV60l; move HV60l before pvzI19; pose proof (proj2 pvzI19) as HV60r; move HV60r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV62l; move HV62l before pvzI20; pose proof (proj2 pvzI20) as HV62r; move HV62r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K3l; move K3l before pvzI21; pose proof (proj2 pvzI21) as K3r; move K3r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K27l; move K27l before pvzI22; pose proof (proj2 pvzI22) as K27r; move K27r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K33l; move K33l before pvzI23; pose proof (proj2 pvzI23) as K33r; move K33r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K42l; move K42l before pvzI24; pose proof (proj2 pvzI24) as K42r; move K42r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K53l; move K53l before pvzI25; pose proof (proj2 pvzI25) as K53r; move K53r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K55l; move K55l before pvzI26; pose proof (proj2 pvzI26) as K55r; move K55r before pvzI26; clear pvzI26.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *. set (vz_62 := V 62%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 45%nat => Z_to_bv 64 vz_45 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | 62%nat => Z_to_bv 64 vz_62 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 45%nat => vz_45 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | 62%nat => vz_62 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 63%nat. }
  assert (HR: regs_ok E PsrdH0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrdH0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrdH0.kn0).
  { unfold know_ok, PsrdH0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39 K49) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39 K49) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39 K49) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39 K49) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39 K48) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39 K48) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | clear - HV2l HV2r K3l K3r K32 K38 K47; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39 K48) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39 K48) | clear; lia | exact K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39 K48) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39 K48) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39 K48; lia | clear - HV36l HV36r K27l K27r K29 K32 K39 K48; lia | clear - HV36l HV36r K27l K27r K29 K32 K39 K48; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39 K48) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39 K48; lia | clear - HV36l HV36r K27l K27r K29 K32 K39 K48; lia | clear - HV36l HV36r K27l K27r K29 K32 K39 K48; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39 K48) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39 K49) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39 K49) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39 K49) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39 K49) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39 K49; lia | clear - HV37l HV37r K33l K33r K35 K38 K39 K49; lia | clear - HV37l HV37r K33l K33r K35 K38 K39 K49; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39 K49) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39 K49; lia | clear - HV37l HV37r K33l K33r K35 K38 K39 K49; lia | clear - HV37l HV37r K33l K33r K35 K38 K39 K49; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39 K49) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39 K49) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39 K48) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39 K48; lia | clear - HV36l HV36r K27l K27r K29 K32 K39 K48; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39 K48) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39 K48; lia | clear - HV36l HV36r K27l K27r K29 K32 K39 K48; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K42l K42r K44 K47 K48 K49) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K42l K42r K44 K47 K48 K49) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K42l K42r K44 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV45l HV45r K42l K42r K44 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K42l K42r K44 K47 K48 K49; lia | clear - HV45l HV45r K42l K42r K44 K47 K48 K49; lia | clear - HV45l HV45r K42l K42r K44 K47 K48 K49; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K42l K42r K44 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K42l K42r K44 K47 K48 K49; lia | clear - HV45l HV45r K42l K42r K44 K47 K48 K49; lia | clear - HV45l HV45r K42l K42r K44 K47 K48 K49; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K42l K42r K44 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39 K48) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K42l K42r K44 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39 K49) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K42l K42r K44 K47 K48 K49) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39 K48) | evalEk ZA ltac:(clear - HV45l HV45r K42l K42r K44 K47 K48 K49) | clear - HV36l HV36r K27l K27r K29 K32 K39 K48; lia | clear - HV36l HV36r K27l K27r K29 K32 K39 K48; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K42l K42r K44 K47 K48 K49) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K42l K42r K44 K47 K48 K49; lia | clear - HV45l HV45r K42l K42r K44 K47 K48 K49; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV45l HV45r K42l K42r K44 K47 K48 K49) | evalEk ZA ltac:(clear - HV62l HV62r K53l K53r) | clear - HV45l HV45r K42l K42r K44 K47 K48 K49; lia | clear - HV45l HV45r K42l K42r K44 K47 K48 K49; lia | byte_tac ltac:(clear - HV62l HV62r K53l K53r) | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV62l HV62r K53l K53r) | exact (conj K53l K53r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K55l K55r) | exact (conj K55l K55r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrdH0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrdH0.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 192) <= bv_unsigned a < (vz_2 - 192) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PsrdH0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38 K47 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PsrdH0.ps0) with 0xb51e4 in Hms. change (SR.ps_regs PsrdH0.ps0) with (map (fun i => (i, nth i PsrdH0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PsrdH0.ps0) with PsrdH0.cells0 in Hcells. unfold PsrdH0.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdH0.regs0 PsrdH0.regs_out0 70 KS_srdH0_0 KS_srdH0_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PsrdH0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk' ZA Hag ltac:(clear) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PsrdH0.ps1) with 0xb5280 in Hms. change (SR.ps_regs PsrdH0.ps1) with (map (fun i => (i, nth i PsrdH0.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PsrdH0.ps1) with PsrdH0.cells1 in Hcells. unfold PsrdH0.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdH0.regs0 PsrdH0.regs_out1 70 KS_srdH0_1 KS_srdH0_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PsrdH0.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk' ZA Hag ltac:(clear) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. 
    change (SR.ps_pc PsrdH0.ps2) with 0xb53b8 in Hms. change (SR.ps_regs PsrdH0.ps2) with (map (fun i => (i, nth i PsrdH0.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PsrdH0.ps2) with PsrdH0.cells2 in Hcells. unfold PsrdH0.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdH0.regs0 PsrdH0.regs_out2 70 KS_srdH0_2 KS_srdH0_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 2 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 9 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 13 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 19 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 20 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 22 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 23 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 24 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 25 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 26 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdH0.regs_out2 E' R' 27 Hregs) by (clear; lia). cbn [nth PsrdH0.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K32 K38 K47) | evalEk' ZA Hag ltac:(clear) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrdRS := LibSegBa_srdRS_b.
Definition KS_srdRS : list nat := Eval vm_compute in (BG.kept_list 70 PsrdRS.regs0 PsrdRS.regs_out0).
Lemma KS_srdRS_ok : BG.kept_ok 70 PsrdRS.regs0 PsrdRS.regs_out0 KS_srdRS = true. Proof. vm_compute. reflexivity. Qed.
Lemma srdRS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 43%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 37%nat) + 1) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 37%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((((V 37%nat) + 16) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 37%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 36%nat) + 256) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 0 -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 192)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u8_at RSEGS M (V 37%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 0 = false -> 1 <= (V 43%nat) <= 16384 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb51e4 M) (st fx' R' 0xd628c M')
        /\ (forall x, In x KS_srdRS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 741924
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 43%nat) + ((V 40%nat) / 2))
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 40%nat) / 2)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 G2 G8 G9 G18 G19 G20 G21 G23 G24 G26 G27 K0 K1 K2 pvzI21 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 pvzI22 K28 K29 K30 K31 K32 pvzI23 K34 K35 K36 K37 K38 K39 K40 pvzI24 K42 pvzI25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV49l; move HV49l before pvzI9; pose proof (proj2 pvzI9) as HV49r; move HV49r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV50l; move HV50l before pvzI10; pose proof (proj2 pvzI10) as HV50r; move HV50r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV51l; move HV51l before pvzI11; pose proof (proj2 pvzI11) as HV51r; move HV51r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV52l; move HV52l before pvzI12; pose proof (proj2 pvzI12) as HV52r; move HV52r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV53l; move HV53l before pvzI13; pose proof (proj2 pvzI13) as HV53r; move HV53r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV54l; move HV54l before pvzI14; pose proof (proj2 pvzI14) as HV54r; move HV54r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV55l; move HV55l before pvzI15; pose proof (proj2 pvzI15) as HV55r; move HV55r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV56l; move HV56l before pvzI16; pose proof (proj2 pvzI16) as HV56r; move HV56r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV57l; move HV57l before pvzI17; pose proof (proj2 pvzI17) as HV57r; move HV57r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV58l; move HV58l before pvzI18; pose proof (proj2 pvzI18) as HV58r; move HV58r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV59l; move HV59l before pvzI19; pose proof (proj2 pvzI19) as HV59r; move HV59r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV60l; move HV60l before pvzI20; pose proof (proj2 pvzI20) as HV60r; move HV60r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K3l; move K3l before pvzI21; pose proof (proj2 pvzI21) as K3r; move K3r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K27l; move K27l before pvzI22; pose proof (proj2 pvzI22) as K27r; move K27r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K33l; move K33l before pvzI23; pose proof (proj2 pvzI23) as K33r; move K33r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K41l; move K41l before pvzI24; pose proof (proj2 pvzI24) as K41r; move K41r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K43l; move K43l before pvzI25; pose proof (proj2 pvzI25) as K43r; move K43r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 43%nat => vz_43 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PsrdRS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrdRS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrdRS.kn0).
  { unfold know_ok, PsrdRS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear; lia | exact K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | byte_tac ltac:(clear - HV40l HV40r K41l K41r) | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | clear; lia | erewrite L5K.land1_bit0_false by first [exact K42 | (clear - HV40l HV40r K41l K41r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K43l K43r) | exact (conj K43l K43r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrdRS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrdRS.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PsrdRS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrdRS.ps0) with 0xd628c in Hms. change (SR.ps_regs PsrdRS.ps0) with (map (fun i => (i, nth i PsrdRS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrdRS.ps0) with PsrdRS.cells0 in Hcells. unfold PsrdRS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdRS.regs0 PsrdRS.regs_out0 70 KS_srdRS KS_srdRS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrdRS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdRS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdRS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdRS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdRS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdRS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdRS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrdRS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PsrdRS.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PsrdRS.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrdRL := LibSegBa_srdRL_b.
Definition KS_srdRL : list nat := Eval vm_compute in (BG.kept_list 70 PsrdRL.regs0 PsrdRL.regs_out0).
Lemma KS_srdRL_ok : BG.kept_ok 70 PsrdRL.regs0 PsrdRL.regs_out0 KS_srdRL = true. Proof. vm_compute. reflexivity. Qed.
Lemma srdRL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 43%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 37%nat) + 1) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 37%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((((V 37%nat) + 16) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 37%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 36%nat) + 256) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 0 -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 192)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u8_at RSEGS M (V 37%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 37%nat) + 8) (V 41%nat) ->
  0 <= (V 41%nat) <= 134217728 -> 1 <= (V 43%nat) <= 16384 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb51e4 M) (st fx' R' 0xd628c M')
        /\ (forall x, In x KS_srdRL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 741924
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 41%nat) + (V 43%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 (V 41%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 G2 G8 G9 G18 G19 G20 G21 G23 G24 G26 G27 K0 K1 K2 pvzI22 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 pvzI23 K28 K29 K30 K31 K32 pvzI24 K34 K35 K36 K37 K38 K39 K40 pvzI25 K42 K43 pvzI26 pvzI27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV49l; move HV49l before pvzI10; pose proof (proj2 pvzI10) as HV49r; move HV49r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV50l; move HV50l before pvzI11; pose proof (proj2 pvzI11) as HV50r; move HV50r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV51l; move HV51l before pvzI12; pose proof (proj2 pvzI12) as HV51r; move HV51r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV52l; move HV52l before pvzI13; pose proof (proj2 pvzI13) as HV52r; move HV52r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV53l; move HV53l before pvzI14; pose proof (proj2 pvzI14) as HV53r; move HV53r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV54l; move HV54l before pvzI15; pose proof (proj2 pvzI15) as HV54r; move HV54r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV55l; move HV55l before pvzI16; pose proof (proj2 pvzI16) as HV55r; move HV55r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV56l; move HV56l before pvzI17; pose proof (proj2 pvzI17) as HV56r; move HV56r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV57l; move HV57l before pvzI18; pose proof (proj2 pvzI18) as HV57r; move HV57r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV58l; move HV58l before pvzI19; pose proof (proj2 pvzI19) as HV58r; move HV58r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV59l; move HV59l before pvzI20; pose proof (proj2 pvzI20) as HV59r; move HV59r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV60l; move HV60l before pvzI21; pose proof (proj2 pvzI21) as HV60r; move HV60r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K3l; move K3l before pvzI22; pose proof (proj2 pvzI22) as K3r; move K3r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K27l; move K27l before pvzI23; pose proof (proj2 pvzI23) as K27r; move K27r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K33l; move K33l before pvzI24; pose proof (proj2 pvzI24) as K33r; move K33r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K41l; move K41l before pvzI25; pose proof (proj2 pvzI25) as K41r; move K41r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K44l; move K44l before pvzI26; pose proof (proj2 pvzI26) as K44r; move K44r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K45l; move K45l before pvzI27; pose proof (proj2 pvzI27) as K45r; move K45r before pvzI27; clear pvzI27.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 43%nat => vz_43 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PsrdRL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrdRL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrdRL.kn0).
  { unfold know_ok, PsrdRL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear; lia | exact K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | byte_tac ltac:(clear - HV40l HV40r K41l K41r) | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | clear; lia | erewrite L5K.land1_bit0_true by first [exact K42 | (clear - HV40l HV40r K41l K41r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear - HV41l HV41r K44l K44r) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K44l K44r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K45l K45r) | exact (conj K45l K45r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrdRL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrdRL.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PsrdRL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrdRL.ps0) with 0xd628c in Hms. change (SR.ps_regs PsrdRL.ps0) with (map (fun i => (i, nth i PsrdRL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrdRL.ps0) with PsrdRL.cells0 in Hcells. unfold PsrdRL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdRL.regs0 PsrdRL.regs_out0 70 KS_srdRL KS_srdRL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrdRL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdRL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdRL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdRL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdRL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdRL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdRL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrdRL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PsrdRL.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PsrdRL.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrdQS := LibSegBa_srdQS_b.
Definition KS_srdQS : list nat := Eval vm_compute in (BG.kept_list 70 PsrdQS.regs0 PsrdQS.regs_out0).
Lemma KS_srdQS_ok : BG.kept_ok 70 PsrdQS.regs0 PsrdQS.regs_out0 KS_srdQS = true. Proof. vm_compute. reflexivity. Qed.
Lemma srdQS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 22) = Z_to_bv 64 (V 46%nat) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 43%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 37%nat) + 1) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 37%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((((V 37%nat) + 16) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 37%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 36%nat) + 256) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 0 -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 192)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u8_at RSEGS M (V 37%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 0 = false -> 1 <= (V 43%nat) <= 16384 ->
  0 <= (V 46%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5224 M) (st fx' R' 0xaed4c M')
        /\ (forall x, In x KS_srdQS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 741996
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 37%nat) + (V 46%nat)) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G26 G27 K0 K1 K2 pvzI22 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 pvzI23 K28 K29 K30 K31 K32 pvzI24 K34 K35 K36 K37 K38 K39 K40 pvzI25 K42 pvzI26 pvzI27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV49l; move HV49l before pvzI10; pose proof (proj2 pvzI10) as HV49r; move HV49r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV50l; move HV50l before pvzI11; pose proof (proj2 pvzI11) as HV50r; move HV50r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV51l; move HV51l before pvzI12; pose proof (proj2 pvzI12) as HV51r; move HV51r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV52l; move HV52l before pvzI13; pose proof (proj2 pvzI13) as HV52r; move HV52r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV53l; move HV53l before pvzI14; pose proof (proj2 pvzI14) as HV53r; move HV53r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV54l; move HV54l before pvzI15; pose proof (proj2 pvzI15) as HV54r; move HV54r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV55l; move HV55l before pvzI16; pose proof (proj2 pvzI16) as HV55r; move HV55r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV56l; move HV56l before pvzI17; pose proof (proj2 pvzI17) as HV56r; move HV56r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV57l; move HV57l before pvzI18; pose proof (proj2 pvzI18) as HV57r; move HV57r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV58l; move HV58l before pvzI19; pose proof (proj2 pvzI19) as HV58r; move HV58r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV59l; move HV59l before pvzI20; pose proof (proj2 pvzI20) as HV59r; move HV59r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV60l; move HV60l before pvzI21; pose proof (proj2 pvzI21) as HV60r; move HV60r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K3l; move K3l before pvzI22; pose proof (proj2 pvzI22) as K3r; move K3r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K27l; move K27l before pvzI23; pose proof (proj2 pvzI23) as K27r; move K27r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K33l; move K33l before pvzI24; pose proof (proj2 pvzI24) as K33r; move K33r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K41l; move K41l before pvzI25; pose proof (proj2 pvzI25) as K41r; move K41r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K43l; move K43l before pvzI26; pose proof (proj2 pvzI26) as K43r; move K43r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K44l; move K44l before pvzI27; pose proof (proj2 pvzI27) as K44r; move K44r before pvzI27; clear pvzI27.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 43%nat => vz_43 | 46%nat => vz_46 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PsrdQS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrdQS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrdQS.kn0).
  { unfold know_ok, PsrdQS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear; lia | exact K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | byte_tac ltac:(clear - HV40l HV40r K41l K41r) | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | clear; lia | erewrite L5K.land1_bit0_false by first [exact K42 | (clear - HV40l HV40r K41l K41r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K43l K43r) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K44l K44r) | exact (conj K44l K44r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrdQS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrdQS.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PsrdQS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrdQS.ps0) with 0xaed4c in Hms. change (SR.ps_regs PsrdQS.ps0) with (map (fun i => (i, nth i PsrdQS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrdQS.ps0) with PsrdQS.cells0 in Hcells. unfold PsrdQS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdQS.regs0 PsrdQS.regs_out0 70 KS_srdQS KS_srdQS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrdQS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdQS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdQS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdQS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdQS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdQS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PsrdQS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrdQS.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrdQL := LibSegBa_srdQL_b.
Definition KS_srdQL : list nat := Eval vm_compute in (BG.kept_list 70 PsrdQL.regs0 PsrdQL.regs_out0).
Lemma KS_srdQL_ok : BG.kept_ok 70 PsrdQL.regs0 PsrdQL.regs_out0 KS_srdQL = true. Proof. vm_compute. reflexivity. Qed.
Lemma srdQL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 22) = Z_to_bv 64 (V 46%nat) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 43%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 37%nat) + 1) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 37%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((((V 37%nat) + 16) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 37%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 36%nat) + 256) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 0 -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 192)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u8_at RSEGS M (V 37%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 37%nat) + 16) (V 42%nat) ->
  4096 <= (V 42%nat) <= 140737488355328 -> 1 <= (V 43%nat) <= 16384 -> 0 <= (V 46%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5224 M) (st fx' R' 0xaed4c M')
        /\ (forall x, In x KS_srdQL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 741996
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + (V 46%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 pvzI22 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G26 G27 K0 K1 K2 pvzI23 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 pvzI24 K28 K29 K30 K31 K32 pvzI25 K34 K35 K36 K37 K38 K39 K40 pvzI26 K42 K43 pvzI27 pvzI28 pvzI29.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV42l; move HV42l before pvzI7; pose proof (proj2 pvzI7) as HV42r; move HV42r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV48l; move HV48l before pvzI10; pose proof (proj2 pvzI10) as HV48r; move HV48r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV49l; move HV49l before pvzI11; pose proof (proj2 pvzI11) as HV49r; move HV49r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV50l; move HV50l before pvzI12; pose proof (proj2 pvzI12) as HV50r; move HV50r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV51l; move HV51l before pvzI13; pose proof (proj2 pvzI13) as HV51r; move HV51r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV52l; move HV52l before pvzI14; pose proof (proj2 pvzI14) as HV52r; move HV52r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV53l; move HV53l before pvzI15; pose proof (proj2 pvzI15) as HV53r; move HV53r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV54l; move HV54l before pvzI16; pose proof (proj2 pvzI16) as HV54r; move HV54r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV55l; move HV55l before pvzI17; pose proof (proj2 pvzI17) as HV55r; move HV55r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV56l; move HV56l before pvzI18; pose proof (proj2 pvzI18) as HV56r; move HV56r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV57l; move HV57l before pvzI19; pose proof (proj2 pvzI19) as HV57r; move HV57r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV58l; move HV58l before pvzI20; pose proof (proj2 pvzI20) as HV58r; move HV58r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV59l; move HV59l before pvzI21; pose proof (proj2 pvzI21) as HV59r; move HV59r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as HV60l; move HV60l before pvzI22; pose proof (proj2 pvzI22) as HV60r; move HV60r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K3l; move K3l before pvzI23; pose proof (proj2 pvzI23) as K3r; move K3r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K27l; move K27l before pvzI24; pose proof (proj2 pvzI24) as K27r; move K27r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K33l; move K33l before pvzI25; pose proof (proj2 pvzI25) as K33r; move K33r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K41l; move K41l before pvzI26; pose proof (proj2 pvzI26) as K41r; move K41r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K44l; move K44l before pvzI27; pose proof (proj2 pvzI27) as K44r; move K44r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K45l; move K45l before pvzI28; pose proof (proj2 pvzI28) as K45r; move K45r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K46l; move K46l before pvzI29; pose proof (proj2 pvzI29) as K46r; move K46r before pvzI29; clear pvzI29.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 42%nat => vz_42 | 43%nat => vz_43 | 46%nat => vz_46 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PsrdQL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrdQL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrdQL.kn0).
  { unfold know_ok, PsrdQL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear; lia | exact K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | byte_tac ltac:(clear - HV40l HV40r K41l K41r) | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | clear; lia | erewrite L5K.land1_bit0_true by first [exact K42 | (clear - HV40l HV40r K41l K41r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear - HV42l HV42r K44l K44r) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K44l K44r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K45l K45r) | exact (conj K45l K45r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K46l K46r) | exact (conj K46l K46r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrdQL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrdQL.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PsrdQL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrdQL.ps0) with 0xaed4c in Hms. change (SR.ps_regs PsrdQL.ps0) with (map (fun i => (i, nth i PsrdQL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrdQL.ps0) with PsrdQL.cells0 in Hcells. unfold PsrdQL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdQL.regs0 PsrdQL.regs_out0 70 KS_srdQL KS_srdQL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrdQL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdQL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdQL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdQL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdQL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdQL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PsrdQL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrdQL.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrdE := LibSegBa_srdE_b.
Definition KS_srdE_0 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdE.regs0 PsrdE.regs_out0).
Lemma KS_srdE_0_ok : BG.kept_ok 70 PsrdE.regs0 PsrdE.regs_out0 KS_srdE_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_srdE_1 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdE.regs0 PsrdE.regs_out1).
Lemma KS_srdE_1_ok : BG.kept_ok 70 PsrdE.regs0 PsrdE.regs_out1 KS_srdE_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_srdE_2 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdE.regs0 PsrdE.regs_out2).
Lemma KS_srdE_2_ok : BG.kept_ok 70 PsrdE.regs0 PsrdE.regs_out2 KS_srdE_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma srdE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 10) = Z_to_bv 64 (V 44%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 22) = Z_to_bv 64 (V 46%nat) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 43%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 37%nat) + 1) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 37%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((((V 37%nat) + 16) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 37%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 36%nat) + 256) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 0 -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 192)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  0 <= (V 44%nat) <= 16384 -> 1 <= (V 43%nat) <= 16384 -> 0 <= (V 46%nat) <= 134217728 -> 1 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb526c M) (st fx' R' 0xd628c M')
        /\ (forall x, In x KS_srdE_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 742204
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 44%nat) + (V 46%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 (V 44%nat)
        /\ 1 <= (((V 44%nat) - (V 43%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb526c M) (st fx' R' 0xb51a0 M')
        /\ (forall x, In x KS_srdE_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 39%nat) - (V 44%nat))
        /\ getr R' (reg 25) = Z_to_bv 64 (V 44%nat)
        /\ 1 <= (((((V 39%nat) + ((18446744073709551615 * (V 44%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64)
        /\ (((V 44%nat) - (V 43%nat)) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb526c M) (st fx' R' 0xb53b8 M')
        /\ (forall x, In x KS_srdE_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 38%nat) + (((-1) * (V 39%nat)) + (V 44%nat)))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 60%nat)
        /\ (((((V 39%nat) + ((18446744073709551615 * (V 44%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ (((V 44%nat) - (V 43%nat)) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G26 G27 K0 K1 K2 pvzI22 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 pvzI23 K28 K29 K30 K31 K32 pvzI24 K34 K35 K36 K37 K38 K39 pvzI25 pvzI26 pvzI27 pvzI28.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV49l; move HV49l before pvzI10; pose proof (proj2 pvzI10) as HV49r; move HV49r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV50l; move HV50l before pvzI11; pose proof (proj2 pvzI11) as HV50r; move HV50r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV51l; move HV51l before pvzI12; pose proof (proj2 pvzI12) as HV51r; move HV51r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV52l; move HV52l before pvzI13; pose proof (proj2 pvzI13) as HV52r; move HV52r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV53l; move HV53l before pvzI14; pose proof (proj2 pvzI14) as HV53r; move HV53r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV54l; move HV54l before pvzI15; pose proof (proj2 pvzI15) as HV54r; move HV54r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV55l; move HV55l before pvzI16; pose proof (proj2 pvzI16) as HV55r; move HV55r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV56l; move HV56l before pvzI17; pose proof (proj2 pvzI17) as HV56r; move HV56r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV57l; move HV57l before pvzI18; pose proof (proj2 pvzI18) as HV57r; move HV57r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV58l; move HV58l before pvzI19; pose proof (proj2 pvzI19) as HV58r; move HV58r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV59l; move HV59l before pvzI20; pose proof (proj2 pvzI20) as HV59r; move HV59r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV60l; move HV60l before pvzI21; pose proof (proj2 pvzI21) as HV60r; move HV60r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K3l; move K3l before pvzI22; pose proof (proj2 pvzI22) as K3r; move K3r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K27l; move K27l before pvzI23; pose proof (proj2 pvzI23) as K27r; move K27r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K33l; move K33l before pvzI24; pose proof (proj2 pvzI24) as K33r; move K33r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K40l; move K40l before pvzI25; pose proof (proj2 pvzI25) as K40r; move K40r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K41l; move K41l before pvzI26; pose proof (proj2 pvzI26) as K41r; move K41r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K42l; move K42l before pvzI27; pose proof (proj2 pvzI27) as K42r; move K42r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K43l; move K43l before pvzI28; pose proof (proj2 pvzI28) as K43r; move K43r before pvzI28; clear pvzI28.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 46%nat => Z_to_bv 64 vz_46 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 43%nat => vz_43 | 44%nat => vz_44 | 46%nat => vz_46 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PsrdE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrdE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrdE.kn0).
  { unfold know_ok, PsrdE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear; lia | exact K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K40l K40r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K43l K43r) | exact (conj K43l K43r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrdE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrdE.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PsrdE.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PsrdE.ps0) with 0xd628c in Hms. change (SR.ps_regs PsrdE.ps0) with (map (fun i => (i, nth i PsrdE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PsrdE.ps0) with PsrdE.cells0 in Hcells. unfold PsrdE.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdE.regs0 PsrdE.regs_out0 70 KS_srdE_0 KS_srdE_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PsrdE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PsrdE.ps1) with 0xb51a0 in Hms. change (SR.ps_regs PsrdE.ps1) with (map (fun i => (i, nth i PsrdE.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PsrdE.ps1) with PsrdE.cells1 in Hcells. unfold PsrdE.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdE.regs0 PsrdE.regs_out1 70 KS_srdE_1 KS_srdE_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PsrdE.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. 
    change (SR.ps_pc PsrdE.ps2) with 0xb53b8 in Hms. change (SR.ps_regs PsrdE.ps2) with (map (fun i => (i, nth i PsrdE.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PsrdE.ps2) with PsrdE.cells2 in Hcells. unfold PsrdE.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdE.regs0 PsrdE.regs_out2 70 KS_srdE_2 KS_srdE_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PsrdE.regs_out2 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out2 E' R' 2 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out2 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out2 E' R' 9 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out2 E' R' 19 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out2 E' R' 20 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out2 E' R' 22 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out2 E' R' 23 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out2 E' R' 24 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out2 E' R' 25 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out2 E' R' 26 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdE.regs_out2 E' R' 27 Hregs) by (clear; lia). cbn [nth PsrdE.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrdF := LibSegBa_srdF_b.
Definition KS_srdF_0 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdF.regs0 PsrdF.regs_out0).
Lemma KS_srdF_0_ok : BG.kept_ok 70 PsrdF.regs0 PsrdF.regs_out0 KS_srdF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_srdF_1 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdF.regs0 PsrdF.regs_out1).
Lemma KS_srdF_1_ok : BG.kept_ok 70 PsrdF.regs0 PsrdF.regs_out1 KS_srdF_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma srdF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 (V 44%nat) -> getr R (reg 26) = Z_to_bv 64 ((V 37%nat) + 1) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 37%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((((V 37%nat) + 16) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 37%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 36%nat) + 256) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 0 -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 192)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  0 <= (V 44%nat) <= 16384 -> 1 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb533c M) (st fx' R' 0xb51a0 M')
        /\ (forall x, In x KS_srdF_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 39%nat) - (V 44%nat))
        /\ 1 <= (((((V 39%nat) + ((18446744073709551615 * (V 44%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb533c M) (st fx' R' 0xb53b8 M')
        /\ (forall x, In x KS_srdF_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 38%nat) + (((-1) * (V 39%nat)) + (V 44%nat)))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 60%nat)
        /\ (((((V 39%nat) + ((18446744073709551615 * (V 44%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G18 G19 G20 G21 G23 G25 G26 G27 K0 K1 K2 pvzI20 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 pvzI21 K28 K29 K30 K31 K32 pvzI22 K34 K35 K36 K37 K38 K39 pvzI23 pvzI24.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV49l; move HV49l before pvzI8; pose proof (proj2 pvzI8) as HV49r; move HV49r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV52l; move HV52l before pvzI11; pose proof (proj2 pvzI11) as HV52r; move HV52r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV53l; move HV53l before pvzI12; pose proof (proj2 pvzI12) as HV53r; move HV53r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV54l; move HV54l before pvzI13; pose proof (proj2 pvzI13) as HV54r; move HV54r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV55l; move HV55l before pvzI14; pose proof (proj2 pvzI14) as HV55r; move HV55r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV56l; move HV56l before pvzI15; pose proof (proj2 pvzI15) as HV56r; move HV56r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV57l; move HV57l before pvzI16; pose proof (proj2 pvzI16) as HV57r; move HV57r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV58l; move HV58l before pvzI17; pose proof (proj2 pvzI17) as HV58r; move HV58r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV59l; move HV59l before pvzI18; pose proof (proj2 pvzI18) as HV59r; move HV59r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV60l; move HV60l before pvzI19; pose proof (proj2 pvzI19) as HV60r; move HV60r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K27l; move K27l before pvzI21; pose proof (proj2 pvzI21) as K27r; move K27r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K33l; move K33l before pvzI22; pose proof (proj2 pvzI22) as K33r; move K33r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K40l; move K40l before pvzI23; pose proof (proj2 pvzI23) as K40r; move K40r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K41l; move K41l before pvzI24; pose proof (proj2 pvzI24) as K41r; move K41r before pvzI24; clear pvzI24.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 44%nat => Z_to_bv 64 vz_44 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 44%nat => vz_44 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PsrdF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrdF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrdF.kn0).
  { unfold know_ok, PsrdF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear; lia | exact K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K40l K40r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrdF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrdF.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PsrdF.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PsrdF.ps0) with 0xb51a0 in Hms. change (SR.ps_regs PsrdF.ps0) with (map (fun i => (i, nth i PsrdF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PsrdF.ps0) with PsrdF.cells0 in Hcells. unfold PsrdF.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdF.regs0 PsrdF.regs_out0 70 KS_srdF_0 KS_srdF_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PsrdF.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. 
    change (SR.ps_pc PsrdF.ps1) with 0xb53b8 in Hms. change (SR.ps_regs PsrdF.ps1) with (map (fun i => (i, nth i PsrdF.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PsrdF.ps1) with PsrdF.cells1 in Hcells. unfold PsrdF.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdF.regs0 PsrdF.regs_out1 70 KS_srdF_1 KS_srdF_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PsrdF.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdF.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdF.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdF.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdF.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdF.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdF.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdF.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdF.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdF.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdF.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdF.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdF.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdF.regs_out1 E' R' 26 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdF.regs_out1 E' R' 27 Hregs) by (clear; lia). cbn [nth PsrdF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrdDS := LibSegBa_srdDS_b.
Definition KS_srdDS : list nat := Eval vm_compute in (BG.kept_list 70 PsrdDS.regs0 PsrdDS.regs_out0).
Lemma KS_srdDS_ok : BG.kept_ok 70 PsrdDS.regs0 PsrdDS.regs_out0 KS_srdDS = true. Proof. vm_compute. reflexivity. Qed.
Lemma srdDS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 16384 -> getr R (reg 26) = Z_to_bv 64 ((V 37%nat) + 1) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 37%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((((V 37%nat) + 16) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 37%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 36%nat) + 256) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 0 -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 192)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u8_at RSEGS M (V 37%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5280 M) (st fx' R' 0xd628c M')
        /\ (forall x, In x KS_srdDS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 742080
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 40%nat) / 2) + 16384)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 40%nat) / 2)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 G2 G8 G9 G18 G19 G20 G21 G23 G24 G26 G27 K0 K1 K2 pvzI20 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 pvzI21 K28 K29 K30 K31 K32 pvzI22 K34 K35 K36 K37 K38 K39 K40 pvzI23 K42.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV49l; move HV49l before pvzI8; pose proof (proj2 pvzI8) as HV49r; move HV49r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV52l; move HV52l before pvzI11; pose proof (proj2 pvzI11) as HV52r; move HV52r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV53l; move HV53l before pvzI12; pose proof (proj2 pvzI12) as HV53r; move HV53r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV54l; move HV54l before pvzI13; pose proof (proj2 pvzI13) as HV54r; move HV54r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV55l; move HV55l before pvzI14; pose proof (proj2 pvzI14) as HV55r; move HV55r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV56l; move HV56l before pvzI15; pose proof (proj2 pvzI15) as HV56r; move HV56r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV57l; move HV57l before pvzI16; pose proof (proj2 pvzI16) as HV57r; move HV57r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV58l; move HV58l before pvzI17; pose proof (proj2 pvzI17) as HV58r; move HV58r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV59l; move HV59l before pvzI18; pose proof (proj2 pvzI18) as HV59r; move HV59r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV60l; move HV60l before pvzI19; pose proof (proj2 pvzI19) as HV60r; move HV60r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K3l; move K3l before pvzI20; pose proof (proj2 pvzI20) as K3r; move K3r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K27l; move K27l before pvzI21; pose proof (proj2 pvzI21) as K27r; move K27r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K33l; move K33l before pvzI22; pose proof (proj2 pvzI22) as K33r; move K33r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K41l; move K41l before pvzI23; pose proof (proj2 pvzI23) as K41r; move K41r before pvzI23; clear pvzI23.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PsrdDS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrdDS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrdDS.kn0).
  { unfold know_ok, PsrdDS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear; lia | exact K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | byte_tac ltac:(clear - HV40l HV40r K41l K41r) | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | clear; lia | erewrite L5K.land1_bit0_false by first [exact K42 | (clear - HV40l HV40r K41l K41r; lia)]; clear; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrdDS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrdDS.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PsrdDS.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrdDS.ps0) with 0xd628c in Hms. change (SR.ps_regs PsrdDS.ps0) with (map (fun i => (i, nth i PsrdDS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrdDS.ps0) with PsrdDS.cells0 in Hcells. unfold PsrdDS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdDS.regs0 PsrdDS.regs_out0 70 KS_srdDS KS_srdDS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrdDS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdDS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdDS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdDS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrdDS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PsrdDS.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PsrdDS.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrdDL := LibSegBa_srdDL_b.
Definition KS_srdDL : list nat := Eval vm_compute in (BG.kept_list 70 PsrdDL.regs0 PsrdDL.regs_out0).
Lemma KS_srdDL_ok : BG.kept_ok 70 PsrdDL.regs0 PsrdDL.regs_out0 KS_srdDL = true. Proof. vm_compute. reflexivity. Qed.
Lemma srdDL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 16384 -> getr R (reg 26) = Z_to_bv 64 ((V 37%nat) + 1) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 37%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((((V 37%nat) + 16) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 37%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 36%nat) + 256) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 0 -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 192)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u8_at RSEGS M (V 37%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 37%nat) + 8) (V 41%nat) ->
  0 <= (V 41%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5280 M) (st fx' R' 0xd628c M')
        /\ (forall x, In x KS_srdDL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 742080
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 41%nat) + 16384)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 (V 41%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 G2 G8 G9 G18 G19 G20 G21 G23 G24 G26 G27 K0 K1 K2 pvzI21 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 pvzI22 K28 K29 K30 K31 K32 pvzI23 K34 K35 K36 K37 K38 K39 K40 pvzI24 K42 K43 pvzI25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV49l; move HV49l before pvzI9; pose proof (proj2 pvzI9) as HV49r; move HV49r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV50l; move HV50l before pvzI10; pose proof (proj2 pvzI10) as HV50r; move HV50r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV51l; move HV51l before pvzI11; pose proof (proj2 pvzI11) as HV51r; move HV51r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV52l; move HV52l before pvzI12; pose proof (proj2 pvzI12) as HV52r; move HV52r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV53l; move HV53l before pvzI13; pose proof (proj2 pvzI13) as HV53r; move HV53r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV54l; move HV54l before pvzI14; pose proof (proj2 pvzI14) as HV54r; move HV54r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV55l; move HV55l before pvzI15; pose proof (proj2 pvzI15) as HV55r; move HV55r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV56l; move HV56l before pvzI16; pose proof (proj2 pvzI16) as HV56r; move HV56r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV57l; move HV57l before pvzI17; pose proof (proj2 pvzI17) as HV57r; move HV57r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV58l; move HV58l before pvzI18; pose proof (proj2 pvzI18) as HV58r; move HV58r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV59l; move HV59l before pvzI19; pose proof (proj2 pvzI19) as HV59r; move HV59r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV60l; move HV60l before pvzI20; pose proof (proj2 pvzI20) as HV60r; move HV60r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K3l; move K3l before pvzI21; pose proof (proj2 pvzI21) as K3r; move K3r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K27l; move K27l before pvzI22; pose proof (proj2 pvzI22) as K27r; move K27r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K33l; move K33l before pvzI23; pose proof (proj2 pvzI23) as K33r; move K33r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K41l; move K41l before pvzI24; pose proof (proj2 pvzI24) as K41r; move K41r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K44l; move K44l before pvzI25; pose proof (proj2 pvzI25) as K44r; move K44r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PsrdDL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrdDL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrdDL.kn0).
  { unfold know_ok, PsrdDL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear; lia | exact K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | byte_tac ltac:(clear - HV40l HV40r K41l K41r) | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | clear; lia | erewrite L5K.land1_bit0_true by first [exact K42 | (clear - HV40l HV40r K41l K41r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear - HV41l HV41r K44l K44r) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K44l K44r) | exact (conj K44l K44r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrdDL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrdDL.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PsrdDL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrdDL.ps0) with 0xd628c in Hms. change (SR.ps_regs PsrdDL.ps0) with (map (fun i => (i, nth i PsrdDL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrdDL.ps0) with PsrdDL.cells0 in Hcells. unfold PsrdDL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdDL.regs0 PsrdDL.regs_out0 70 KS_srdDL KS_srdDL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrdDL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdDL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdDL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdDL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdDL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdDL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdDL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrdDL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PsrdDL.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PsrdDL.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrdD2 := LibSegBa_srdD2_b.
Definition KS_srdD2 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdD2.regs0 PsrdD2.regs_out0).
Lemma KS_srdD2_ok : BG.kept_ok 70 PsrdD2.regs0 PsrdD2.regs_out0 KS_srdD2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma srdD2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 22) = Z_to_bv 64 (V 46%nat) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 16384 -> getr R (reg 26) = Z_to_bv 64 ((V 37%nat) + 1) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 37%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((((V 37%nat) + 16) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 37%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 36%nat) + 256) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 0 -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 192)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u8_at RSEGS M (V 37%nat) (V 40%nat) -> 0 <= (V 40%nat) <= 255 -> Z.testbit (V 40%nat) 0 = true -> L5.u64_at RSEGS M ((V 37%nat) + 16) (V 42%nat) ->
  4096 <= (V 42%nat) <= 140737488355328 -> 0 <= (V 46%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb52c0 M) (st fx' R' 0xb29f8 M')
        /\ (forall x, In x KS_srdD2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 742152
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + (V 46%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 16384).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 G26 G27 K0 K1 K2 pvzI22 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 pvzI23 K28 K29 K30 K31 K32 pvzI24 K34 K35 K36 K37 K38 K39 K40 pvzI25 K42 K43 pvzI26 pvzI27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV42l; move HV42l before pvzI7; pose proof (proj2 pvzI7) as HV42r; move HV42r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV49l; move HV49l before pvzI10; pose proof (proj2 pvzI10) as HV49r; move HV49r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV50l; move HV50l before pvzI11; pose proof (proj2 pvzI11) as HV50r; move HV50r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV51l; move HV51l before pvzI12; pose proof (proj2 pvzI12) as HV51r; move HV51r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV52l; move HV52l before pvzI13; pose proof (proj2 pvzI13) as HV52r; move HV52r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV53l; move HV53l before pvzI14; pose proof (proj2 pvzI14) as HV53r; move HV53r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV54l; move HV54l before pvzI15; pose proof (proj2 pvzI15) as HV54r; move HV54r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV55l; move HV55l before pvzI16; pose proof (proj2 pvzI16) as HV55r; move HV55r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV56l; move HV56l before pvzI17; pose proof (proj2 pvzI17) as HV56r; move HV56r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV57l; move HV57l before pvzI18; pose proof (proj2 pvzI18) as HV57r; move HV57r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV58l; move HV58l before pvzI19; pose proof (proj2 pvzI19) as HV58r; move HV58r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV59l; move HV59l before pvzI20; pose proof (proj2 pvzI20) as HV59r; move HV59r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV60l; move HV60l before pvzI21; pose proof (proj2 pvzI21) as HV60r; move HV60r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K3l; move K3l before pvzI22; pose proof (proj2 pvzI22) as K3r; move K3r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K27l; move K27l before pvzI23; pose proof (proj2 pvzI23) as K27r; move K27r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K33l; move K33l before pvzI24; pose proof (proj2 pvzI24) as K33r; move K33r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K41l; move K41l before pvzI25; pose proof (proj2 pvzI25) as K41r; move K41r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K44l; move K44l before pvzI26; pose proof (proj2 pvzI26) as K44r; move K44r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K45l; move K45l before pvzI27; pose proof (proj2 pvzI27) as K45r; move K45r before pvzI27; clear pvzI27.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 46%nat => Z_to_bv 64 vz_46 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 42%nat => vz_42 | 46%nat => vz_46 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PsrdD2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrdD2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrdD2.kn0).
  { unfold know_ok, PsrdD2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear; lia | exact K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | byte_tac ltac:(clear - HV40l HV40r K41l K41r) | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV40l HV40r K41l K41r) | clear; lia | erewrite L5K.land1_bit0_true by first [exact K42 | (clear - HV40l HV40r K41l K41r; lia)]; clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear - HV42l HV42r K44l K44r) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K44l K44r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K45l K45r) | exact (conj K45l K45r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrdD2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrdD2.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PsrdD2.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PsrdD2.ps0) with 0xb29f8 in Hms. change (SR.ps_regs PsrdD2.ps0) with (map (fun i => (i, nth i PsrdD2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PsrdD2.ps0) with PsrdD2.cells0 in Hcells. unfold PsrdD2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdD2.regs0 PsrdD2.regs_out0 70 KS_srdD2 KS_srdD2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PsrdD2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdD2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PsrdD2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdD2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PsrdD2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrdD2.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PsrdD3 := LibSegBa_srdD3_b.
Definition KS_srdD3_0 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdD3.regs0 PsrdD3.regs_out0).
Lemma KS_srdD3_0_ok : BG.kept_ok 70 PsrdD3.regs0 PsrdD3.regs_out0 KS_srdD3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_srdD3_1 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdD3.regs0 PsrdD3.regs_out1).
Lemma KS_srdD3_1_ok : BG.kept_ok 70 PsrdD3.regs0 PsrdD3.regs_out1 KS_srdD3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_srdD3_2 : list nat := Eval vm_compute in (BG.kept_list 70 PsrdD3.regs0 PsrdD3.regs_out2).
Lemma KS_srdD3_2_ok : BG.kept_ok 70 PsrdD3.regs0 PsrdD3.regs_out2 KS_srdD3_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma srdD3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 58%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 60%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 (V 39%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 10) = Z_to_bv 64 (V 44%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 272) -> getr R (reg 20) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 22) = Z_to_bv 64 (V 46%nat) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 272) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 16384 -> getr R (reg 26) = Z_to_bv 64 ((V 37%nat) + 1) -> getr R (reg 27) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487360 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 192) 192 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 58%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 60%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) ((V 37%nat) + 8) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) ((V 37%nat) + 16) -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((((V 37%nat) + 16) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 136) ((((V 37%nat) + 8) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 144) ((V 36%nat) + 256) ->
  L5.u64_at RSEGS M ((V 2%nat) - 152) ((((V 36%nat) + 256) / 8) + 2147450880) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) 0 -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 192) + 192 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 192)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 192) + 192 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 192)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.defined M ((V 36%nat) + 256) 8 -> 0 <= (V 44%nat) <= 16384 -> 0 <= (V 46%nat) <= 134217728 -> 1 <= (V 39%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5308 M) (st fx' R' 0xd628c M')
        /\ (forall x, In x KS_srdD3_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 742204
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 44%nat) + (V 46%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 (V 44%nat)
        /\ 1 <= (((V 44%nat) - 16384) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb5308 M) (st fx' R' 0xb51a0 M')
        /\ (forall x, In x KS_srdD3_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 39%nat) - (V 44%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 256)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 44%nat)
        /\ 1 <= (((((V 39%nat) + ((18446744073709551615 * (V 44%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64)
        /\ (((V 44%nat) - 16384) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb5308 M) (st fx' R' 0xb53b8 M')
        /\ (forall x, In x KS_srdD3_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 38%nat) + (((-1) * (V 39%nat)) + (V 44%nat)))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 36%nat) + 256)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 57%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 58%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 60%nat)
        /\ (((((V 39%nat) + ((18446744073709551615 * (V 44%nat)) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ (((V 44%nat) - 16384) mod 2 ^ 64) < 1)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G26 G27 K0 K1 K2 pvzI21 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 pvzI22 K28 K29 K30 K31 K32 pvzI23 K34 K35 K36 K37 K38 K39 K40 pvzI24 pvzI25 pvzI26.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV46l; move HV46l before pvzI7; pose proof (proj2 pvzI7) as HV46r; move HV46r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV49l; move HV49l before pvzI9; pose proof (proj2 pvzI9) as HV49r; move HV49r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV50l; move HV50l before pvzI10; pose proof (proj2 pvzI10) as HV50r; move HV50r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV51l; move HV51l before pvzI11; pose proof (proj2 pvzI11) as HV51r; move HV51r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV52l; move HV52l before pvzI12; pose proof (proj2 pvzI12) as HV52r; move HV52r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV53l; move HV53l before pvzI13; pose proof (proj2 pvzI13) as HV53r; move HV53r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV54l; move HV54l before pvzI14; pose proof (proj2 pvzI14) as HV54r; move HV54r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV55l; move HV55l before pvzI15; pose proof (proj2 pvzI15) as HV55r; move HV55r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV56l; move HV56l before pvzI16; pose proof (proj2 pvzI16) as HV56r; move HV56r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV57l; move HV57l before pvzI17; pose proof (proj2 pvzI17) as HV57r; move HV57r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV58l; move HV58l before pvzI18; pose proof (proj2 pvzI18) as HV58r; move HV58r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV59l; move HV59l before pvzI19; pose proof (proj2 pvzI19) as HV59r; move HV59r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV60l; move HV60l before pvzI20; pose proof (proj2 pvzI20) as HV60r; move HV60r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K3l; move K3l before pvzI21; pose proof (proj2 pvzI21) as K3r; move K3r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K27l; move K27l before pvzI22; pose proof (proj2 pvzI22) as K27r; move K27r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K33l; move K33l before pvzI23; pose proof (proj2 pvzI23) as K33r; move K33r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K41l; move K41l before pvzI24; pose proof (proj2 pvzI24) as K41r; move K41r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K42l; move K42l before pvzI25; pose proof (proj2 pvzI25) as K42r; move K42r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K43l; move K43l before pvzI26; pose proof (proj2 pvzI26) as K43r; move K43r before pvzI26; clear pvzI26.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_58 := V 58%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_60 := V 60%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 44%nat => Z_to_bv 64 vz_44 | 46%nat => Z_to_bv 64 vz_46 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 58%nat => Z_to_bv 64 vz_58 | 59%nat => Z_to_bv 64 vz_59 | 60%nat => Z_to_bv 64 vz_60 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 44%nat => vz_44 | 46%nat => vz_46 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 58%nat => vz_58 | 59%nat => vz_59 | 60%nat => vz_60 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 61%nat. }
  assert (HR: regs_ok E PsrdD3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PsrdD3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PsrdD3.kn0).
  { unfold know_ok, PsrdD3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV58l HV58r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV59l HV59r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV60l HV60r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K32 K38; lia | clear - HV2l HV2r K3l K3r K32 K38; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | clear; lia | exact K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | clear; lia | exact K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | clear - HV37l HV37r K33l K33r K35 K38 K39; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K32 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K33l K33r K35 K38 K39) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | clear - HV36l HV36r K27l K27r K29 K32 K39; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K41l K41r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K43l K43r) | exact (conj K43l K43r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PsrdD3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PsrdD3.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PsrdD3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K27l K27r K29 K32 K39) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K27l K27r K29 K32 K39 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PsrdD3.ps0) with 0xd628c in Hms. change (SR.ps_regs PsrdD3.ps0) with (map (fun i => (i, nth i PsrdD3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PsrdD3.ps0) with PsrdD3.cells0 in Hcells. unfold PsrdD3.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdD3.regs0 PsrdD3.regs_out0 70 KS_srdD3_0 KS_srdD3_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PsrdD3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PsrdD3.ps1) with 0xb51a0 in Hms. change (SR.ps_regs PsrdD3.ps1) with (map (fun i => (i, nth i PsrdD3.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PsrdD3.ps1) with PsrdD3.cells1 in Hcells. unfold PsrdD3.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdD3.regs0 PsrdD3.regs_out1 70 KS_srdD3_1 KS_srdD3_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PsrdD3.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. 
    change (SR.ps_pc PsrdD3.ps2) with 0xb53b8 in Hms. change (SR.ps_regs PsrdD3.ps2) with (map (fun i => (i, nth i PsrdD3.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PsrdD3.ps2) with PsrdD3.cells2 in Hcells. unfold PsrdD3.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PsrdD3.regs0 PsrdD3.regs_out2 70 KS_srdD3_2 KS_srdD3_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 1 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 2 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 8 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 9 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 19 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 20 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 22 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 23 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 24 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 25 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 26 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PsrdD3.regs_out2 E' R' 27 Hregs) by (clear; lia). cbn [nth PsrdD3.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

End PMASRDP.
