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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_arpA_b LibSegBa_arpR0_b LibSegBa_arpB_b LibSegBa_arpF_b LibSegBa_arpSS_b LibSegBa_arpSL_b LibSegBa_arpES_b LibSegBa_arpEL_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMARSPP.
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
Module ParpA := LibSegBa_arpA_b.
Definition KS_arpA_0 : list nat := Eval vm_compute in (BG.kept_list 60 ParpA.regs0 ParpA.regs_out0).
Lemma KS_arpA_0_ok : BG.kept_ok 60 ParpA.regs0 ParpA.regs_out0 KS_arpA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arpA_1 : list nat := Eval vm_compute in (BG.kept_list 60 ParpA.regs0 ParpA.regs_out1).
Lemma KS_arpA_1_ok : BG.kept_ok 60 ParpA.regs0 ParpA.regs_out1 KS_arpA_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arpA_2 : list nat := Eval vm_compute in (BG.kept_list 60 ParpA.regs0 ParpA.regs_out2).
Lemma KS_arpA_2_ok : BG.kept_ok 60 ParpA.regs0 ParpA.regs_out2 KS_arpA_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arpA_3 : list nat := Eval vm_compute in (BG.kept_list 60 ParpA.regs0 ParpA.regs_out3).
Lemma KS_arpA_3_ok : BG.kept_ok 60 ParpA.regs0 ParpA.regs_out3 KS_arpA_3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arpA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 38%nat) -> getr R (reg 12) = Z_to_bv 64 (V 37%nat) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) -> 0 <= (V 33%nat) <= 16384 -> 0 <= (V 38%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb4dc0 M) (st fx' R' 0xb501c M')
        /\ (forall x, In x KS_arpA_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ (((V 38%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0xb4dc0 M) (st fx' R' 0xb4ee0 M')
        /\ (forall x, In x KS_arpA_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ (V 38%nat) <= (V 33%nat)
        /\ 1 <= (((V 33%nat) - 0) mod 2 ^ 64)
        /\ 1 <= (((V 38%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0xb4dc0 M) (st fx' R' 0xb4e9c M')
        /\ (forall x, In x KS_arpA_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ (V 33%nat) < (V 38%nat)
        /\ 1 <= (((V 33%nat) - 0) mod 2 ^ 64)
        /\ 1 <= (((V 38%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0xb4dc0 M) (st fx' R' 0xb4e20 M')
        /\ (forall x, In x KS_arpA_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ (((V 33%nat) - 0) mod 2 ^ 64) < 1
        /\ 1 <= (((V 38%nat) - 0) mod 2 ^ 64)
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
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G10 G11 G12 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 pvzI8 pvzI9.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K13l; move K13l before pvzI8; pose proof (proj2 pvzI8) as K13r; move K13r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K14l; move K14l before pvzI9; pose proof (proj2 pvzI9) as K14r; move K14r before pvzI9; clear pvzI9.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E ParpA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParpA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParpA.kn0).
  { unfold know_ok, ParpA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear - HV33l HV33r K13l K13r) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParpA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParpA.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 80) <= bv_unsigned a < (vz_2 - 80) + 80) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold ParpA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc ParpA.ps0) with 0xb501c in Hms. change (SR.ps_regs ParpA.ps0) with (map (fun i => (i, nth i ParpA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParpA.ps0) with ParpA.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParpA.regs0 ParpA.regs_out0 60 KS_arpA_0 KS_arpA_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParpA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParpA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParpA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc ParpA.ps1) with 0xb4ee0 in Hms. change (SR.ps_regs ParpA.ps1) with (map (fun i => (i, nth i ParpA.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParpA.ps1) with ParpA.cells1 in Hcells. unfold ParpA.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParpA.regs0 ParpA.regs_out1 60 KS_arpA_1 KS_arpA_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParpA.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth ParpA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth ParpA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth ParpA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth ParpA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth ParpA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth ParpA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth ParpA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth ParpA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out1 E' R' 22 Hregs) by (clear; lia). cbn [nth ParpA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc ParpA.ps2) with 0xb4e9c in Hms. change (SR.ps_regs ParpA.ps2) with (map (fun i => (i, nth i ParpA.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParpA.ps2) with ParpA.cells2 in Hcells. unfold ParpA.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParpA.regs0 ParpA.regs_out2 60 KS_arpA_2 KS_arpA_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParpA.regs_out2 E' R' 2 Hregs) by (clear; lia). cbn [nth ParpA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out2 E' R' 8 Hregs) by (clear; lia). cbn [nth ParpA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out2 E' R' 9 Hregs) by (clear; lia). cbn [nth ParpA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth ParpA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth ParpA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth ParpA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out2 E' R' 19 Hregs) by (clear; lia). cbn [nth ParpA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth ParpA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out2 E' R' 22 Hregs) by (clear; lia). cbn [nth ParpA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right. 
    change (SR.ps_pc ParpA.ps3) with 0xb4e20 in Hms. change (SR.ps_regs ParpA.ps3) with (map (fun i => (i, nth i ParpA.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParpA.ps3) with ParpA.cells3 in Hcells. unfold ParpA.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParpA.regs0 ParpA.regs_out3 60 KS_arpA_3 KS_arpA_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParpA.regs_out3 E' R' 2 Hregs) by (clear; lia). cbn [nth ParpA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out3 E' R' 8 Hregs) by (clear; lia). cbn [nth ParpA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out3 E' R' 9 Hregs) by (clear; lia). cbn [nth ParpA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out3 E' R' 10 Hregs) by (clear; lia). cbn [nth ParpA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out3 E' R' 18 Hregs) by (clear; lia). cbn [nth ParpA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out3 E' R' 19 Hregs) by (clear; lia). cbn [nth ParpA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out3 E' R' 21 Hregs) by (clear; lia). cbn [nth ParpA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpA.regs_out3 E' R' 22 Hregs) by (clear; lia). cbn [nth ParpA.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParpR0 := LibSegBa_arpR0_b.
Definition KS_arpR0_0 : list nat := Eval vm_compute in (BG.kept_list 60 ParpR0.regs0 ParpR0.regs_out0).
Lemma KS_arpR0_0_ok : BG.kept_ok 60 ParpR0.regs0 ParpR0.regs_out0 KS_arpR0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arpR0_1 : list nat := Eval vm_compute in (BG.kept_list 60 ParpR0.regs0 ParpR0.regs_out1).
Lemma KS_arpR0_1_ok : BG.kept_ok 60 ParpR0.regs0 ParpR0.regs_out1 KS_arpR0_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arpR0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 38%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> 1 <= (V 38%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb4e20 M) (st fx' R' 0xb4e9c M')
        /\ (forall x, In x KS_arpR0_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ 16384 < (V 38%nat))
      \/ (msteps RSEGS (st fx R 0xb4e20 M) (st fx' R' 0xb29f8 M')
        /\ (forall x, In x KS_arpR0_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 740956
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 16384
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 36%nat) + 264)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 36%nat) + 264) / 8) + 2147450880)
        /\ (V 38%nat) <= 16384)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G21 G22 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 K12 K13 K14 pvzI8.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K15l; move K15l before pvzI8; pose proof (proj2 pvzI8) as K15r; move K15r before pvzI8; clear pvzI8.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E ParpR0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParpR0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParpR0.kn0).
  { unfold know_ok, ParpR0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParpR0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParpR0.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParpR0.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc ParpR0.ps0) with 0xb4e9c in Hms. change (SR.ps_regs ParpR0.ps0) with (map (fun i => (i, nth i ParpR0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParpR0.ps0) with ParpR0.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParpR0.regs0 ParpR0.regs_out0 60 KS_arpR0_0 KS_arpR0_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParpR0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParpR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpR0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParpR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpR0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParpR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
  - right.
    change (SR.ps_pc ParpR0.ps1) with 0xb29f8 in Hms. change (SR.ps_regs ParpR0.ps1) with (map (fun i => (i, nth i ParpR0.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParpR0.ps1) with ParpR0.cells1 in Hcells. unfold ParpR0.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParpR0.regs0 ParpR0.regs_out1 60 KS_arpR0_1 KS_arpR0_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParpR0.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth ParpR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpR0.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth ParpR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpR0.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth ParpR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpR0.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth ParpR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpR0.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth ParpR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpR0.regs_out1 E' R' 23 Hregs) by (clear; lia). cbn [nth ParpR0.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParpB := LibSegBa_arpB_b.
Definition KS_arpB_0 : list nat := Eval vm_compute in (BG.kept_list 60 ParpB.regs0 ParpB.regs_out0).
Lemma KS_arpB_0_ok : BG.kept_ok 60 ParpB.regs0 ParpB.regs_out0 KS_arpB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_arpB_1 : list nat := Eval vm_compute in (BG.kept_list 60 ParpB.regs0 ParpB.regs_out1).
Lemma KS_arpB_1_ok : BG.kept_ok 60 ParpB.regs0 ParpB.regs_out1 KS_arpB_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma arpB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 38%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 10) = Z_to_bv 64 (V 43%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 20) = Z_to_bv 64 ((V 36%nat) + 264) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 36%nat) + 264) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> 0 <= (V 43%nat) <= 16384 -> 1 <= (V 38%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 280) <= bv_unsigned a < ((V 36%nat) + 280) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 280) <= i < ((V 36%nat) + 280) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb4e5c M) (st fx' R' 0xb4e9c M')
        /\ (forall x, In x KS_arpB_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)
        /\ (V 43%nat) < (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) (V 43%nat))
      \/ (msteps RSEGS (st fx R 0xb4e5c M) (st fx' R' 0xb4ee0 M')
        /\ (forall x, In x KS_arpB_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 43%nat)
        /\ (V 38%nat) <= (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) (V 43%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 pvzI9 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV36l; move HV36l before pvzI3; pose proof (proj2 pvzI3) as HV36r; move HV36r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV37l; move HV37l before pvzI4; pose proof (proj2 pvzI4) as HV37r; move HV37r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV38l; move HV38l before pvzI5; pose proof (proj2 pvzI5) as HV38r; move HV38r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K13l; move K13l before pvzI9; pose proof (proj2 pvzI9) as K13r; move K13r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K14l; move K14l before pvzI10; pose proof (proj2 pvzI10) as K14r; move K14r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E ParpB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParpB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParpB.kn0).
  { unfold know_ok, ParpB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParpB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParpB.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 280) <= bv_unsigned a < (vz_36 + 280) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold ParpB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K6l K6r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_pair in Hnth. destruct Hnth as [[-> ->] | [-> ->]].
  - left.
    change (SR.ps_pc ParpB.ps0) with 0xb4e9c in Hms. change (SR.ps_regs ParpB.ps0) with (map (fun i => (i, nth i ParpB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParpB.ps0) with ParpB.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParpB.regs0 ParpB.regs_out0 60 KS_arpB_0 KS_arpB_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParpB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParpB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParpB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParpB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K13l K13r) | clear; lia]. 
  - right.
    change (SR.ps_pc ParpB.ps1) with 0xb4ee0 in Hms. change (SR.ps_regs ParpB.ps1) with (map (fun i => (i, nth i ParpB.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells ParpB.ps1) with ParpB.cells1 in Hcells. unfold ParpB.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' ParpB.regs0 ParpB.regs_out1 60 KS_arpB_1 KS_arpB_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg ParpB.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth ParpB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpB.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth ParpB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg ParpB.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth ParpB.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K6l K6r) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K13l K13r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParpF := LibSegBa_arpF_b.
Definition KS_arpF : list nat := Eval vm_compute in (BG.kept_list 60 ParpF.regs0 ParpF.regs_out0).
Lemma KS_arpF_ok : BG.kept_ok 60 ParpF.regs0 ParpF.regs_out0 KS_arpF = true. Proof. vm_compute. reflexivity. Qed.
Lemma arpF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 38%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> 1 <= (V 35%nat) <= 140737488355328 -> L5.defined M ((V 36%nat) + 256) 8 ->
  1 <= (V 33%nat) <= 16384 -> 1 <= (V 38%nat) <= 16384 -> 0 <= ((V 33%nat) - (V 38%nat)) <= 16383 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 8) -> ~ (((V 36%nat) + 280) <= bv_unsigned a < ((V 36%nat) + 280) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 8) -> ~ (((V 36%nat) + 280) <= i < ((V 36%nat) + 280) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb4ee0 M) (st fx' R' 0xb501c M')
        /\ (forall x, In x KS_arpF -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 35%nat) + (V 38%nat))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) ((V 33%nat) - (V 38%nat))
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) ((V 35%nat) + (V 38%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G12 G18 G19 G21 G22 K0 K1 K2 pvzI16 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 pvzI17 K16 K17 K18 K19 K20 K21 pvzI18 K23 pvzI19 pvzI20 pvzI21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV45l; move HV45l before pvzI8; pose proof (proj2 pvzI8) as HV45r; move HV45r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV49l; move HV49l before pvzI12; pose proof (proj2 pvzI12) as HV49r; move HV49r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV50l; move HV50l before pvzI13; pose proof (proj2 pvzI13) as HV50r; move HV50r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV51l; move HV51l before pvzI14; pose proof (proj2 pvzI14) as HV51r; move HV51r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV52l; move HV52l before pvzI15; pose proof (proj2 pvzI15) as HV52r; move HV52r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K3l; move K3l before pvzI16; pose proof (proj2 pvzI16) as K3r; move K3r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K15l; move K15l before pvzI17; pose proof (proj2 pvzI17) as K15r; move K15r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K22l; move K22l before pvzI18; pose proof (proj2 pvzI18) as K22r; move K22r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K24l; move K24l before pvzI19; pose proof (proj2 pvzI19) as K24r; move K24r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K25l; move K25l before pvzI20; pose proof (proj2 pvzI20) as K25r; move K25r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K26l; move K26l before pvzI21; pose proof (proj2 pvzI21) as K26r; move K26r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E ParpF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParpF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParpF.kn0).
  { unfold know_ok, ParpF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K15l K15r; lia | clear - HV36l HV36r K15l K15r; lia | clear - HV36l HV36r K15l K15r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K15l K15r; lia | clear - HV36l HV36r K15l K15r; lia | clear - HV36l HV36r K15l K15r; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear - HV35l HV35r K22l K22r) | clear - HV36l HV36r K15l K15r; lia | clear - HV36l HV36r K15l K15r; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K15l K15r; lia | clear - HV36l HV36r K15l K15r; lia | clear - HV36l HV36r K15l K15r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K24l K24r K26l K26r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K25l K25r K26l K26r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K24l K24r K26l K26r HV38l HV38r K25l K25r) | exact (conj K26l K26r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParpF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParpF.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 8) -> ~ ((vz_36 + 280) <= bv_unsigned a < (vz_36 + 280) + 16) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold ParpF.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K15l K15r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K15l K15r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K15l K15r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K15l K15r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParpF.ps0) with 0xb501c in Hms. change (SR.ps_regs ParpF.ps0) with (map (fun i => (i, nth i ParpF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParpF.ps0) with ParpF.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParpF.regs0 ParpF.regs_out0 60 KS_arpF KS_arpF_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParpF.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpF.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth ParpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpF.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth ParpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpF.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth ParpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpF.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpF.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpF.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth ParpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpF.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth ParpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpF.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth ParpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpF.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth ParpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpF.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth ParpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpF.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth ParpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpF.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth ParpF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K15l K15r) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K24l K24r K26l K26r HV38l HV38r K25l K25r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K15l K15r) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K22l K22r HV38l HV38r K25l K25r K26l K26r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParpSS := LibSegBa_arpSS_b.
Definition KS_arpSS : list nat := Eval vm_compute in (BG.kept_list 60 ParpSS.regs0 ParpSS.regs_out0).
Lemma KS_arpSS_ok : BG.kept_ok 60 ParpSS.regs0 ParpSS.regs_out0 KS_arpSS = true. Proof. vm_compute. reflexivity. Qed.
Lemma arpSS_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 38%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 ->
  L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) -> L5.u8_at RSEGS M (V 37%nat) (V 39%nat) ->
  0 <= (V 39%nat) <= 255 -> Z.testbit (V 39%nat) 0 = false -> L5KA.zeros_at M ((((V 37%nat) + 1) / 8) + 2147450880) 1 -> 1 <= (V 38%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) + 0) <= bv_unsigned a < ((V 37%nat) + 0) + 2) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) + 0) <= i < ((V 37%nat) + 0) + 2) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb4e9c M) (st fx' R' 0xb50e0 M')
        /\ (forall x, In x KS_arpSS -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 741280
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' (V 37%nat) 0
        /\ L5.u8_at RSEGS M' ((V 37%nat) + 1) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G9 G18 G19 G21 G22 K0 K1 K2 pvzI6 K4 K5 pvzI7 K7 K8 K9 K10 K11 pvzI8 K13 K14 K15 K16 K17 K18 K19 pvzI9 K21 K22 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K6l; move K6l before pvzI7; pose proof (proj2 pvzI7) as K6r; move K6r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K12l; move K12l before pvzI8; pose proof (proj2 pvzI8) as K12r; move K12r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K20l; move K20l before pvzI9; pose proof (proj2 pvzI9) as K20r; move K20r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K23l; move K23l before pvzI10; pose proof (proj2 pvzI10) as K23r; move K23r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E ParpSS.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParpSS.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParpSS.kn0).
  { unfold know_ok, ParpSS.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r; lia | clear - HV37l HV37r K12l K12r; lia | clear - HV37l HV37r K12l K12r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r; lia | clear - HV37l HV37r K12l K12r; lia | clear - HV37l HV37r K12l K12r; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear - HV39l HV39r K20l K20r K21) | clear - HV37l HV37r K12l K12r; lia | clear - HV37l HV37r K12l K12r; lia | byte_tac ltac:(clear - HV39l HV39r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_false vz_39 ltac:(clear - HV39l HV39r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r; lia | clear - HV37l HV37r K12l K12r; lia | clear - HV37l HV37r K12l K12r; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParpSS.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParpSS.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_37 + 0) <= bv_unsigned a < (vz_37 + 0) + 2) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold ParpSS.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K12l K12r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParpSS.ps0) with 0xb50e0 in Hms. change (SR.ps_regs ParpSS.ps0) with (map (fun i => (i, nth i ParpSS.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParpSS.ps0) with ParpSS.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParpSS.regs0 ParpSS.regs_out0 60 KS_arpSS KS_arpSS_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParpSS.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParpSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpSS.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParpSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpSS.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParpSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpSS.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParpSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpSS.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth ParpSS.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParpSL := LibSegBa_arpSL_b.
Definition KS_arpSL : list nat := Eval vm_compute in (BG.kept_list 60 ParpSL.regs0 ParpSL.regs_out0).
Lemma KS_arpSL_ok : BG.kept_ok 60 ParpSL.regs0 ParpSL.regs_out0 KS_arpSL = true. Proof. vm_compute. reflexivity. Qed.
Lemma arpSL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 38%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 -> (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) ->
  6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 ->
  L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) -> L5.u8_at RSEGS M (V 37%nat) (V 39%nat) ->
  0 <= (V 39%nat) <= 255 -> Z.testbit (V 39%nat) 0 = true -> L5.u64_at RSEGS M ((V 37%nat) + 8) (V 40%nat) -> L5.u64_at RSEGS M ((V 37%nat) + 16) (V 41%nat) ->
  4096 <= (V 41%nat) <= 140737488355320 -> aligned (V 41%nat) 8 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> L5KA.zeros_at M (((V 41%nat) / 8) + 2147450880) 1 ->
  L5.writable RSEGS M (V 41%nat) 1 -> (((V 2%nat) - 80) + 80 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 80)) -> ((V 41%nat) + 1 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 41%nat)) -> ((V 41%nat) + 1 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 41%nat)) ->
  1 <= (V 38%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> ~ (((V 37%nat) + 8) <= bv_unsigned a < ((V 37%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 1) -> ~ (((V 37%nat) + 8) <= i < ((V 37%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb4e9c M) (st fx' R' 0xb50e0 M')
        /\ (forall x, In x KS_arpSL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 741280
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 37%nat) + 8) 0
        /\ L5.u8_at RSEGS M' (V 41%nat) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 G2 G8 G9 G18 G19 G21 G22 K0 K1 K2 pvzI8 K4 K5 pvzI9 K7 K8 K9 K10 K11 pvzI10 K13 K14 K15 K16 K17 K18 K19 pvzI11 K21 K22 K23 pvzI12 K25 K26 K27 K28 K29 K30 K31 pvzI13.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K6l; move K6l before pvzI9; pose proof (proj2 pvzI9) as K6r; move K6r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K12l; move K12l before pvzI10; pose proof (proj2 pvzI10) as K12r; move K12r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K20l; move K20l before pvzI11; pose proof (proj2 pvzI11) as K20r; move K20r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K24l; move K24l before pvzI12; pose proof (proj2 pvzI12) as K24r; move K24r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K32l; move K32l before pvzI13; pose proof (proj2 pvzI13) as K32r; move K32r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E ParpSL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParpSL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParpSL.kn0).
  { unfold know_ok, ParpSL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | clear - HV36l HV36r K6l K6r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r; lia | clear - HV37l HV37r K12l K12r; lia | clear - HV37l HV37r K12l K12r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K12l K12r; lia | clear - HV37l HV37r K12l K12r; lia | clear - HV37l HV37r K12l K12r; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear - HV39l HV39r K20l K20r K21) | clear - HV37l HV37r K12l K12r; lia | clear - HV37l HV37r K12l K12r; lia | byte_tac ltac:(clear - HV39l HV39r K20l K20r K21) | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K20l K20r K21) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K20l K20r K21) | clear; lia | rewrite (L5K.land1_bit0_true vz_39 ltac:(clear - HV39l HV39r K20l K20r K21; lia) K21); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV37l HV37r K12l K12r; lia | clear - HV37l HV37r K12l K12r; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear - HV41l HV41r K24l K24r) | clear - HV37l HV37r K12l K12r; lia | clear - HV37l HV37r K12l K12r; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K24l K24r) | clear; lia | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K24l K24r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV41l HV41r K24l K24r) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K24l K24r; lia | clear - HV41l HV41r K24l K24r; lia | clear - HV41l HV41r K24l K24r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K24l K24r) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K24l K24r; lia | clear - HV41l HV41r K24l K24r; lia | clear - HV41l HV41r K24l K24r; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K24l K24r) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K24l K24r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K12l K12r) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K24l K24r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K6l K6r) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K32l K32r) | exact (conj K32l K32r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParpSL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParpSL.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_41 + 0) <= bv_unsigned a < (vz_41 + 0) + 1) -> ~ ((vz_37 + 8) <= bv_unsigned a < (vz_37 + 8) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold ParpSL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV41l HV41r K24l K24r) | evalEk' ZA Hag ltac:(clear) | clear - HV41l HV41r K24l K24r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K12l K12r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParpSL.ps0) with 0xb50e0 in Hms. change (SR.ps_regs ParpSL.ps0) with (map (fun i => (i, nth i ParpSL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParpSL.ps0) with ParpSL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParpSL.regs0 ParpSL.regs_out0 60 KS_arpSL KS_arpSL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParpSL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParpSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpSL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParpSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpSL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParpSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpSL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth ParpSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpSL.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth ParpSL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K12l K12r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV41l HV41r K24l K24r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParpES := LibSegBa_arpES_b.
Definition KS_arpES : list nat := Eval vm_compute in (BG.kept_list 60 ParpES.regs0 ParpES.regs_out0).
Lemma KS_arpES_ok : BG.kept_ok 60 ParpES.regs0 ParpES.regs_out0 KS_arpES = true. Proof. vm_compute. reflexivity. Qed.
Lemma arpES_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 38%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u8_at RSEGS M (V 37%nat) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> Z.testbit (V 39%nat) 0 = false -> 1 <= (V 38%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb4fa0 M) (st fx' R' 0xb501c M')
        /\ (forall x, In x KS_arpES -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 37%nat) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 39%nat) / 2)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 G2 G8 G9 G18 G19 G21 G22 K0 K1 K2 pvzI15 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 pvzI16 K16 K17 K18 K19 K20 pvzI17 K22 K23 K24 K25 K26 K27 K28 pvzI18 K30 pvzI19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV44l; move HV44l before pvzI6; pose proof (proj2 pvzI6) as HV44r; move HV44r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV45l; move HV45l before pvzI7; pose proof (proj2 pvzI7) as HV45r; move HV45r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV47l; move HV47l before pvzI9; pose proof (proj2 pvzI9) as HV47r; move HV47r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV48l; move HV48l before pvzI10; pose proof (proj2 pvzI10) as HV48r; move HV48r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV49l; move HV49l before pvzI11; pose proof (proj2 pvzI11) as HV49r; move HV49r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV50l; move HV50l before pvzI12; pose proof (proj2 pvzI12) as HV50r; move HV50r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV51l; move HV51l before pvzI13; pose proof (proj2 pvzI13) as HV51r; move HV51r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV52l; move HV52l before pvzI14; pose proof (proj2 pvzI14) as HV52r; move HV52r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K3l; move K3l before pvzI15; pose proof (proj2 pvzI15) as K3r; move K3r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K15l; move K15l before pvzI16; pose proof (proj2 pvzI16) as K15r; move K15r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K21l; move K21l before pvzI17; pose proof (proj2 pvzI17) as K21r; move K21r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K29l; move K29l before pvzI18; pose proof (proj2 pvzI18) as K29r; move K29r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K31l; move K31l before pvzI19; pose proof (proj2 pvzI19) as K31r; move K31r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E ParpES.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParpES.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParpES.kn0).
  { unfold know_ok, ParpES.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K15l K15r; lia | clear - HV36l HV36r K15l K15r; lia | clear - HV36l HV36r K15l K15r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K15l K15r; lia | clear - HV36l HV36r K15l K15r; lia | clear - HV36l HV36r K15l K15r; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear - HV39l HV39r K29l K29r K30) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | byte_tac ltac:(clear - HV39l HV39r K29l K29r K30) | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K29l K29r K30) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K29l K29r K30) | clear; lia | rewrite (L5K.land1_bit0_false vz_39 ltac:(clear - HV39l HV39r K29l K29r K30; lia) K30); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K31l K31r) | exact (conj K31l K31r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParpES.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParpES.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParpES.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParpES.ps0) with 0xb501c in Hms. change (SR.ps_regs ParpES.ps0) with (map (fun i => (i, nth i ParpES.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParpES.ps0) with ParpES.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParpES.regs0 ParpES.regs_out0 60 KS_arpES KS_arpES_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParpES.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpES.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth ParpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpES.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth ParpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpES.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth ParpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpES.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpES.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpES.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth ParpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpES.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth ParpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpES.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth ParpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpES.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth ParpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpES.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth ParpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParpES.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth ParpES.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module ParpEL := LibSegBa_arpEL_b.
Definition KS_arpEL : list nat := Eval vm_compute in (BG.kept_list 60 ParpEL.regs0 ParpEL.regs_out0).
Lemma KS_arpEL_ok : BG.kept_ok 60 ParpEL.regs0 ParpEL.regs_out0 KS_arpEL = true. Proof. vm_compute. reflexivity. Qed.
Lemma arpEL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 38%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 (V 36%nat) -> getr R (reg 19) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487248 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> 6905856 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  (((V 2%nat) - 80) + 80 <= (V 36%nat) \/ (V 36%nat) + 296 <= ((V 2%nat) - 80)) -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) ->
  L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 80) + 80 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 80)) -> ((V 36%nat) + 296 <= (V 37%nat) \/ (V 37%nat) + 24 <= (V 36%nat)) ->
  L5.u8_at RSEGS M (V 37%nat) (V 39%nat) -> 0 <= (V 39%nat) <= 255 -> Z.testbit (V 39%nat) 0 = true -> L5.u64_at RSEGS M ((V 37%nat) + 8) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 37%nat) + 16) (V 41%nat) -> 1 <= (V 38%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb4fa0 M) (st fx' R' 0xb501c M')
        /\ (forall x, In x KS_arpEL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 G2 G8 G9 G18 G19 G21 G22 K0 K1 K2 pvzI17 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 pvzI18 K16 K17 K18 K19 K20 pvzI19 K22 K23 K24 K25 K26 K27 K28 pvzI20 K30 K31 K32 pvzI21.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV40l; move HV40l before pvzI6; pose proof (proj2 pvzI6) as HV40r; move HV40r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV41l; move HV41l before pvzI7; pose proof (proj2 pvzI7) as HV41r; move HV41r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV44l; move HV44l before pvzI8; pose proof (proj2 pvzI8) as HV44r; move HV44r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV45l; move HV45l before pvzI9; pose proof (proj2 pvzI9) as HV45r; move HV45r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV46l; move HV46l before pvzI10; pose proof (proj2 pvzI10) as HV46r; move HV46r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV47l; move HV47l before pvzI11; pose proof (proj2 pvzI11) as HV47r; move HV47r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV48l; move HV48l before pvzI12; pose proof (proj2 pvzI12) as HV48r; move HV48r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV49l; move HV49l before pvzI13; pose proof (proj2 pvzI13) as HV49r; move HV49r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV50l; move HV50l before pvzI14; pose proof (proj2 pvzI14) as HV50r; move HV50r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV51l; move HV51l before pvzI15; pose proof (proj2 pvzI15) as HV51r; move HV51r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV52l; move HV52l before pvzI16; pose proof (proj2 pvzI16) as HV52r; move HV52r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K3l; move K3l before pvzI17; pose proof (proj2 pvzI17) as K3r; move K3r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K15l; move K15l before pvzI18; pose proof (proj2 pvzI18) as K15r; move K15r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K21l; move K21l before pvzI19; pose proof (proj2 pvzI19) as K21r; move K21r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K29l; move K29l before pvzI20; pose proof (proj2 pvzI20) as K29r; move K29r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K33l; move K33l before pvzI21; pose proof (proj2 pvzI21) as K33r; move K33r before pvzI21; clear pvzI21.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 44%nat => Z_to_bv 64 vz_44 | 45%nat => Z_to_bv 64 vz_45 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 39%nat => vz_39 | 40%nat => vz_40 | 41%nat => vz_41 | 44%nat => vz_44 | 45%nat => vz_45 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 53%nat. }
  assert (HR: regs_ok E ParpEL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl ParpEL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M ParpEL.kn0).
  { unfold know_ok, ParpEL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | clear; lia | exact K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K15l K15r; lia | clear - HV36l HV36r K15l K15r; lia | clear - HV36l HV36r K15l K15r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K15l K15r; lia | clear - HV36l HV36r K15l K15r; lia | clear - HV36l HV36r K15l K15r; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | clear; lia | exact K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K15l K15r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear - HV39l HV39r K29l K29r K30) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | byte_tac ltac:(clear - HV39l HV39r K29l K29r K30) | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K29l K29r K30) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV39l HV39r K29l K29r K30) | clear; lia | rewrite (L5K.land1_bit0_true vz_39 ltac:(clear - HV39l HV39r K29l K29r K30; lia) K30); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K21l K21r) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV37l HV37r K21l K21r; lia | clear - HV37l HV37r K21l K21r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (ParpEL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change ParpEL.NX0 with 60%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold ParpEL.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc ParpEL.ps0) with 0xb501c in Hms. change (SR.ps_regs ParpEL.ps0) with (map (fun i => (i, nth i ParpEL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells ParpEL.ps0) with ParpEL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' ParpEL.regs0 ParpEL.regs_out0 60 KS_arpEL KS_arpEL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg ParpEL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth ParpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpEL.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth ParpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpEL.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth ParpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpEL.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth ParpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpEL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth ParpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpEL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth ParpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpEL.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth ParpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpEL.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth ParpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpEL.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth ParpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpEL.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth ParpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg ParpEL.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth ParpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg ParpEL.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth ParpEL.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End PMARSPP.
