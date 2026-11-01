(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_adkD2_b LibSegBa_adkRH_b LibSegBa_adkRF_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADP6.
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
Module PadkD2 := LibSegBa_adkD2_b.
Definition KS_adkD2_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkD2.regs0 PadkD2.regs_out0).
Lemma KS_adkD2_0_ok : BG.kept_ok 80 PadkD2.regs0 PadkD2.regs_out0 KS_adkD2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkD2_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkD2.regs0 PadkD2.regs_out1).
Lemma KS_adkD2_1_ok : BG.kept_ok 80 PadkD2.regs0 PadkD2.regs_out1 KS_adkD2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkD2_2 : list nat := Eval vm_compute in (BG.kept_list 80 PadkD2.regs0 PadkD2.regs_out2).
Lemma KS_adkD2_2_ok : BG.kept_ok 80 PadkD2.regs0 PadkD2.regs_out2 KS_adkD2_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkD2_3 : list nat := [1; 2; 3; 4; 6; 7; 8; 9; 18; 21; 24; 28; 29; 30; 31]%nat.
Lemma KS_adkD2_3_ok : BG.kept_ok 80 PadkD2.regs0 PadkD2.regs_out3 KS_adkD2_3 = true. Proof. now vm_compute. Qed.
Lemma adkD2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 35%nat) -> getr R (reg 11) = Z_to_bv 64 (V 36%nat) -> getr R (reg 12) = Z_to_bv 64 (V 37%nat) -> getr R (reg 13) = Z_to_bv 64 (V 39%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 34%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 30) = Z_to_bv 64 (V 38%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> L5.img_clear M 65536 1282048 ->
  0 <= (V 39%nat) <= 4294967295 -> 0 <= (V 37%nat) <= 7 -> 4096 <= (V 50%nat) <= 140737488354816 -> 4096 <= (V 33%nat) <= 140737488355280 ->
  4096 <= (V 34%nat) <= 140737488355312 -> 0 <= ((V 38%nat) - (V 33%nat)) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 240) <= bv_unsigned a < ((V 2%nat) - 240) + 64) -> ~ (((V 2%nat) - 168) <= bv_unsigned a < ((V 2%nat) - 168) + 8) -> ~ (((V 2%nat) - 136) <= bv_unsigned a < ((V 2%nat) - 136) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 240) <= i < ((V 2%nat) - 240) + 64) -> ~ (((V 2%nat) - 168) <= i < ((V 2%nat) - 168) + 8) -> ~ (((V 2%nat) - 136) <= i < ((V 2%nat) - 136) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb40a4 M) (st fx' R' 0xb425c M')
        /\ (forall x, In x KS_adkD2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
        /\ getr R' (reg 10) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAluw Instr.ALU_ADD (EVar 35) (ELit 0))
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 12) = Z_to_bv 64 (V 37%nat)
        /\ bv_unsigned (getr R' (reg 13)) = ((V 35%nat) / 4294967296)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 15) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_ADD (EVar 2) (ELit (-136)))
        /\ bv_unsigned (getr R' (reg 16)) = 18446744073709551603
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 39%nat) / 131072)
        /\ bv_unsigned (getr R' (reg 29)) = (bv_unsigned (getr R (reg 29)))
        /\ bv_unsigned (getr R' (reg 30)) = (V 38%nat)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 35) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EVar 37)) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (EVar 36)) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ ((((V 35%nat) / 4294967296) - 0) mod 2 ^ 64) < 1
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) ((V 35%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 136) ((((16384 * (V 37%nat)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb40a4 M) (st fx' R' 0xb4164 M')
        /\ (forall x, In x KS_adkD2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
        /\ getr R' (reg 6) = getr R (reg 6)
        /\ getr R' (reg 10) = Z_to_bv 64 3
        /\ getr R' (reg 11) = Z_to_bv 64 18446744072850558976
        /\ getr R' (reg 12) = Z_to_bv 64 1000001536
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 35%nat) / 4294967296)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 39%nat) / 131072)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 1000000000
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 23) = Z_to_bv 64 14757395259826634752
        /\ getr R' (reg 25) = Z_to_bv 64 19342813113834067
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 50%nat) + 172)
        /\ getr R' (reg 27) = Z_to_bv 64 10
        /\ bv_unsigned (getr R' (reg 29)) = (bv_unsigned (getr R (reg 29)))
        /\ bv_unsigned (getr R' (reg 30)) = (V 38%nat)
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 35) (ELit 0)) (ELit 0)) (ELit 1))) <= 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 50%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (((V 50%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) ((V 39%nat) / 131072)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 16383
        /\ ((((V 35%nat) / 4294967296) - 0) mod 2 ^ 64) < 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EVar 37)) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (EVar 36)) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) ((V 35%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 136) ((((16384 * (V 37%nat)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb40a4 M) (st fx' R' 0xb4164 M')
        /\ (forall x, In x KS_adkD2_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
        /\ getr R' (reg 6) = getr R (reg 6)
        /\ getr R' (reg 10) = Z_to_bv 64 3
        /\ getr R' (reg 11) = Z_to_bv 64 18446744072850558976
        /\ getr R' (reg 12) = Z_to_bv 64 1000001536
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 35%nat) / 4294967296)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 39%nat) / 131072)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 1000000000
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 23) = Z_to_bv 64 14757395259826634752
        /\ getr R' (reg 25) = Z_to_bv 64 19342813113834067
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 50%nat) + 172)
        /\ getr R' (reg 27) = Z_to_bv 64 10
        /\ bv_unsigned (getr R' (reg 29)) = (bv_unsigned (getr R (reg 29)))
        /\ bv_unsigned (getr R' (reg 30)) = (V 38%nat)
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ 1 <= ((((V 35%nat) / 4294967296) - 0) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EVar 37)) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (EVar 36)) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 50%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (((V 50%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) ((V 39%nat) / 131072)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 16383
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) ((V 35%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 136) ((((16384 * (V 37%nat)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb40a4 M) (st fx' R' 0xb4164 M')
        /\ (forall x, In x KS_adkD2_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
        /\ getr R' (reg 6) = getr R (reg 6)
        /\ getr R' (reg 10) = Z_to_bv 64 3
        /\ getr R' (reg 11) = Z_to_bv 64 18446744072850558976
        /\ getr R' (reg 12) = Z_to_bv 64 1000001536
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 35%nat) / 4294967296)
        /\ getr R' (reg 14) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EVar 37)) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383)))
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 39%nat) / 131072)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 1000000000
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 23) = Z_to_bv 64 14757395259826634752
        /\ getr R' (reg 25) = Z_to_bv 64 19342813113834067
        /\ getr R' (reg 26) = Z_to_bv 64 ((V 50%nat) + 172)
        /\ getr R' (reg 27) = Z_to_bv 64 10
        /\ bv_unsigned (getr R' (reg 29)) = (bv_unsigned (getr R (reg 29)))
        /\ bv_unsigned (getr R' (reg 30)) = (V 38%nat)
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EVar 37)) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (EVar 36)) (ELit 0)) (ELit 0)) (ELit 1))) <= 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 50%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (((V 50%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) ((V 39%nat) / 131072)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 16383
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) ((V 35%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 136) ((((16384 * (V 37%nat)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64))).
Proof.
  intros w2 w33 w34 w35 w36 w37 w38 w39 w50 r2 r8 r9 r10 r11 r12 r13 r18 r19 r20 r23 r24 r26 r27 r30
    sp_box sp_al fr_wr img k39 k37 k50 k33 k34 k38.
  match goal with |- context [edenot ?env0 _] => set (Ein := env0) end.
  pose (num := fun j : nat => match j with
                              | 2%nat => V 2%nat | 33%nat => V 33%nat | 34%nat => V 34%nat | 35%nat => V 35%nat
                              | 36%nat => V 36%nat | 37%nat => V 37%nat | 38%nat => V 38%nat | 39%nat => V 39%nat
                              | 50%nat => V 50%nat
                              | _ => bv_unsigned (getr R (reg j))
                              end).
  assert (num_ok : forall j, bv_unsigned (ev Ein j) = num j).
  { intro j. unfold Ein, num; cbn [ev].
    do 51 (destruct j as [|j]; [cbn beta iota; first [reflexivity | apply BG.unsigned_lit; assumption] |]).
    reflexivity. }
  assert (regsE : regs_ok Ein PadkD2.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity |]. cbn [PadkD2.regs0 tl BG.slots].
    repeat split; slotP num_ok. }
  assert (knE : know_ok RSEGS Ein M PadkD2.kn0).
  { unfold know_ok, PadkD2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk num_ok idtac | lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk num_ok idtac | lia | exact sp_al]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk num_ok idtac | evalEk num_ok idtac | lia | lia | lia | exactA fr_wr]. }
    apply Forall_cons. { apply L5K.kentry_KImg; [lia | lia | exact img]. }
    do 6 (apply Forall_cons; [eapply L5K.kentry_KRange; [evalEk num_ok idtac | lia] |]).
    apply Forall_nil. }
  destruct (PadkD2.seg_sound_ax fx Ein R M regsE knE (Forall_nil _))
    as (fxo & Eout & Ro & Mo & k & ps & pick & agE & run & outs & _ & _ & frame & cellsF & grows).
  assert (hi35_ltu : bv_unsigned (edenot Eout (EAlu ALU_SLTU (EAlu ALU_SUB (EAlu ALU_SRL (EVar 35) (ELit 32)) (ELit 0)) (ELit 1)))
                     = if (V 35%nat / 4294967296 - 0) mod 2 ^ 64 <? 1 then 1 else 0).
  { L5K.evalB' num_ok agE. unfold num. reflexivity. }
  exists fxo, Ro, Mo.
  split; [exact grows |].
  match goal with |- ?F /\ _ => assert (keep : F) end.
  { intros a n240 n168 n136. apply frame. unfold PadkD2.F0.
    repeat (eapply L5K.outside_cons_e; [evalEk' num_ok agE idtac | evalEk' num_ok agE idtac | lia |]).
    apply L5K.outside_nil_e. }
  split; [exact keep |].
  split. { intros i i_rng n240 n168 n136. apply keep; rewrite BG.unsigned_lit by lia; assumption. }
  change PadkD2.PSS with [PadkD2.ps0; PadkD2.ps1; PadkD2.ps2; PadkD2.ps3] in pick.
  destruct k as [|[|[|[|k]]]]; cbn [nth_error] in pick; [ | | | | destruct k; cbn in pick; discriminate pick ];
    injection pick as <-.
  1: left. 2: (right; left). 3: (right; right; left). 4: (right; right; right).
  1: pose proof (BG.kept_regs Ein Eout R Ro _ _ 80 _ KS_adkD2_0_ok regsE agE outs) as kept.
  2: pose proof (BG.kept_regs Ein Eout R Ro _ _ 80 _ KS_adkD2_1_ok regsE agE outs) as kept.
  3: pose proof (BG.kept_regs Ein Eout R Ro _ _ 80 _ KS_adkD2_2_ok regsE agE outs) as kept.
  4: pose proof (BG.kept_regs Ein Eout R Ro _ _ 80 _ KS_adkD2_3_ok regsE agE outs) as kept.
  all: pose proof (fun i lt => BG.out_reg _ Eout Ro i outs lt) as outE.
  all: repeat lazymatch goal with |- _ <= ?x <= _ => fail | |- _ /\ _ => split end.
  all: try lazymatch goal with
    | |- msteps _ _ _ => exact run
    | |- forall x, In x _ -> _ => exact kept
    | |- getr _ ?r = getr _ ?r => apply kept, L5K.in_b; reflexivity
    | |- bv_unsigned (getr _ ?r) = bv_unsigned (getr _ ?r) => f_equal; apply kept, L5K.in_b; reflexivity
    end.
  all: try lazymatch goal with
    | |- context [getr _ (Z_to_bv 5 (Z.of_nat ?n))] => rewrite (outE n ltac:(lia)); L5K.norm_expr
    end.
  all: try lazymatch goal with
    | |- edenot _ _ = edenot _ _ => apply (BG.edenot_kept 80); [exact agE | reflexivity]
    | |- edenot _ _ = Z_to_bv 64 _ => wordP' num_ok agE
    | |- bv_unsigned (edenot _ _) = _ => evalEk' num_ok agE zfacts
    end.
  all: try lazymatch goal with
    | |- ?lo <= bv_unsigned (edenot _ ?e) <= ?hi =>
        rewrite <- (BG.edenot_kept 80 Ein Eout e agE eq_refl); exact (cellsF (KRange e lo hi) ltac:(cbn; tauto))
    | |- context [(?v / 4294967296 - 0) mod 2 ^ 64] =>
        let c := fresh "c" in
        pose proof (cellsF (KRange (EAlu ALU_SLTU (EAlu ALU_SUB (EAlu ALU_SRL (EVar 35) (ELit 32)) (ELit 0)) (ELit 1)) _ _)
                      ltac:(cbn; repeat (first [left; reflexivity | right]))) as c;
        cbn [kentry_ok] in c; rewrite hi35_ltu in c; revert c;
        case (Z.ltb_spec ((v / 4294967296 - 0) mod 2 ^ 64) 1); intros ? c; lia
    end.
  all: lazymatch goal with
    | |- L5.u64_at _ _ (_ - ?n) _ =>
        eapply (u64_of_KWord8a Eout Mo (EVar 2) (- n));
        [ apply cellsF; cbn; repeat (first [left; reflexivity | right])
        | evalEk' num_ok agE idtac | evalEk' num_ok agE zfacts | lia ]
    | |- L5.u32_at _ _ (_ - ?n) _ =>
        eapply (u32_of_KWord4a Eout Mo (EVar 2) (- n));
        [ apply cellsF; cbn; repeat (first [left; reflexivity | right])
        | evalEk' num_ok agE idtac | first [evalEk' num_ok agE zfacts | L5K.evalB' num_ok agE; unfold num; reflexivity] | lia ]
    end.
Qed.
(* [comment removed for export] *)

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
        /\ getr R' (reg 31) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EVar 31)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 42%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 41%nat)).
Proof.
  intros w2 w40 w41 w42 w50 r2 r8 r9 r10 r18 r19 r20 r22 r23 r25 r26 r27 sp_box sp_al fr_wr k40 k50 m136 m128.
  match goal with |- context [edenot ?env0 _] => set (Ein := env0) end.
  pose (num := fun j : nat => match j with
                              | 2%nat => V 2%nat | 40%nat => V 40%nat | 41%nat => V 41%nat
                              | 42%nat => V 42%nat | 50%nat => V 50%nat
                              | _ => bv_unsigned (getr R (reg j))
                              end).
  assert (num_ok : forall j, bv_unsigned (ev Ein j) = num j).
  { intro j. unfold Ein, num; cbn [ev].
    do 51 (destruct j as [|j]; [cbn beta iota; first [reflexivity | apply BG.unsigned_lit; assumption] |]).
    reflexivity. }
  assert (regsE : regs_ok Ein PadkRH.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity |]. cbn [PadkRH.regs0 tl BG.slots].
    repeat split; slotP num_ok. }
  assert (knE : know_ok RSEGS Ein M PadkRH.kn0).
  { unfold know_ok, PadkRH.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk num_ok idtac | lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk num_ok idtac | lia | exact sp_al]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk num_ok idtac | evalEk num_ok idtac | lia | lia | lia | exactA fr_wr]. }
    do 2 (apply Forall_cons; [eapply L5K.kentry_KRange; [evalEk num_ok idtac | lia] |]).
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk num_ok idtac | evalEk num_ok idtac | lia | lia | exactA m136]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk num_ok idtac | evalEk num_ok idtac | lia | lia | exactA m128]. }
    apply Forall_nil. }
  destruct (PadkRH.seg_sound_ax fx Ein R M regsE knE (Forall_nil _))
    as (fxo & Eout & Ro & Mo & k & ps & pick & agE & run & outs & _ & _ & frame & cellsF & grows).
  exists fxo, Ro, Mo.
  split; [exact grows |].
  match goal with |- ?F /\ _ => assert (keep : F) end.
  { intros a n120. apply frame. unfold PadkRH.F0.
    eapply L5K.outside_cons_e; [evalEk' num_ok agE idtac | evalEk' num_ok agE idtac | lia | apply L5K.outside_nil_e]. }
  split; [exact keep |].
  split. { intros i i_rng n120. apply keep; rewrite BG.unsigned_lit by lia; assumption. }
  change PadkRH.PSS with [PadkRH.ps0] in pick. apply L5K.nth_error_single in pick. subst ps.
  pose proof (BG.kept_regs Ein Eout R Ro _ _ 80 _ KS_adkRH_ok regsE agE outs) as kept.
  pose proof (fun i lt => BG.out_reg _ Eout Ro i outs lt) as outE.
  repeat split.
  all: try lazymatch goal with
    | |- msteps _ _ _ => exact run
    | |- forall x, In x _ -> _ => exact kept
    | |- getr _ ?r = getr _ ?r => apply kept, L5K.in_b; reflexivity
    | |- bv_unsigned (getr _ ?r) = bv_unsigned (getr _ ?r) => f_equal; apply kept, L5K.in_b; reflexivity
    end.
  all: try lazymatch goal with
    | |- context [getr _ (Z_to_bv 5 (Z.of_nat ?n))] => rewrite (outE n ltac:(lia)); L5K.norm_expr
    end.
  all: try lazymatch goal with
    | |- edenot _ _ = edenot _ _ => apply (BG.edenot_kept 80); [exact agE | reflexivity]
    | |- edenot _ _ = Z_to_bv 64 _ => wordP' num_ok agE
    end.
  all: lazymatch goal with
    | |- L5.u64_at _ _ (_ - ?n) _ =>
        eapply (u64_of_KWord8a Eout Mo (EVar 2) (- n));
        [ apply cellsF; cbn; repeat (first [left; reflexivity | right])
        | evalEk' num_ok agE idtac | evalEk' num_ok agE idtac | lia ]
    end.
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
        /\ getr R' (reg 29) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EVar 29)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 42)) (ELit 0)) (ELit 1))) <= 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 0 4 (EVar 42)) (ELit 0)) (ELit 1))) <= 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 41)) (ELit 0)) (ELit 1))) <= 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1))) <= 1)
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
        /\ getr R' (reg 29) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EVar 29)
        /\ getr R' (reg 30) = getr R (reg 30)
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 0 4 (EVar 42)) (ELit 0)) (ELit 1))) <= 0
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EExt true 4 4 (EVar 41)) (ELit 0)) (ELit 1))) <= 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb417c M) (st fx' R' 0xb41c8 M')
        /\ (forall x, In x KS_adkRF_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 120)
        /\ getr R' (reg 18) = Z_to_bv 64 (((36 * (V 40%nat)) + (V 50%nat)) + 28)
        /\ getr R' (reg 21) = Z_to_bv 64 0
        /\ getr R' (reg 28) = getr R (reg 28)
        /\ getr R' (reg 29) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EVar 29)
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
        /\ getr R' (reg 29) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EVar 29)
        /\ getr R' (reg 30) = getr R (reg 30)
        /\ getr R' (reg 31) = getr R (reg 31)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 41) (ELit 0)) (ELit 0)) (ELit 1))) <= 0)).
Proof.
  intros w2 w40 w41 w42 w50 r2 r8 r9 r10 r11 r12 r18 r19 r20 r22 r23 r24 r25 r26 r27 m112 m120
    sp_box sp_al fr_wr k40 k50 m136 m128.
  match goal with |- context [edenot ?env0 _] => set (Ein := env0) in * end.
  pose (num := fun j : nat => match j with
                              | 2%nat => V 2%nat | 40%nat => V 40%nat | 41%nat => V 41%nat
                              | 42%nat => V 42%nat | 50%nat => V 50%nat
                              | _ => bv_unsigned (getr R (reg j))
                              end).
  assert (num_ok : forall j, bv_unsigned (ev Ein j) = num j).
  { intro j. unfold Ein, num; cbn [ev].
    do 51 (destruct j as [|j]; [cbn beta iota; first [reflexivity | apply BG.unsigned_lit; assumption] |]).
    reflexivity. }
  assert (regsE : regs_ok Ein PadkRF.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity |]. cbn [PadkRF.regs0 tl BG.slots].
    repeat split; slotP num_ok. }
  assert (knE : know_ok RSEGS Ein M PadkRF.kn0).
  { unfold know_ok, PadkRF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk num_ok idtac | evalEk num_ok idtac | lia | lia | exactA m112]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk num_ok idtac | evalEk num_ok idtac | lia | lia | exactA m120]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk num_ok idtac | lia]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk num_ok idtac | lia | exact sp_al]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk num_ok idtac | evalEk num_ok idtac | lia | lia | lia | exactA fr_wr]. }
    do 2 (apply Forall_cons; [eapply L5K.kentry_KRange; [evalEk num_ok idtac | lia] |]).
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk num_ok idtac | evalEk num_ok idtac | lia | lia | exactA m136]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk num_ok idtac | evalEk num_ok idtac | lia | lia | exactA m128]. }
    apply Forall_nil. }
  destruct (PadkRF.seg_sound_ax fx Ein R M regsE knE (Forall_nil _))
    as (fxo & Eout & Ro & Mo & k & ps & pick & agE & run & outs & _ & _ & frame & cellsF & grows).
  exists fxo, Ro, Mo.
  assert (keep : forall a : word, Mo a = M a) by (intro a; apply frame; apply L5K.outside_nil_e).
  split; [exact grows |]. split; [exact keep |]. split; [intros i _; apply keep |].
  change PadkRF.PSS with [PadkRF.ps0; PadkRF.ps1; PadkRF.ps2; PadkRF.ps3; PadkRF.ps4] in pick.
  destruct k as [|[|[|[|[|k]]]]]; cbn [nth_error] in pick; [ | | | | | destruct k; cbn in pick; discriminate pick ];
    injection pick as <-.
  1: left. 2: (right; left). 3: (right; right; left). 4: (right; right; right; left). 5: (right; right; right; right).
  1: pose proof (BG.kept_regs Ein Eout R Ro _ _ 80 _ KS_adkRF_0_ok regsE agE outs) as kept.
  2: pose proof (BG.kept_regs Ein Eout R Ro _ _ 80 _ KS_adkRF_1_ok regsE agE outs) as kept.
  3: pose proof (BG.kept_regs Ein Eout R Ro _ _ 80 _ KS_adkRF_2_ok regsE agE outs) as kept.
  4: pose proof (BG.kept_regs Ein Eout R Ro _ _ 80 _ KS_adkRF_3_ok regsE agE outs) as kept.
  5: pose proof (BG.kept_regs Ein Eout R Ro _ _ 80 _ KS_adkRF_4_ok regsE agE outs) as kept.
  all: pose proof (fun i lt => BG.out_reg _ Eout Ro i outs lt) as outE.
  all: repeat lazymatch goal with |- _ <= ?x <= _ => fail | |- _ /\ _ => split end.
  all: try lazymatch goal with
    | |- msteps _ _ _ => exact run
    | |- forall x, In x _ -> _ => exact kept
    | |- getr _ ?r = getr _ ?r => apply kept, L5K.in_b; reflexivity
    end.
  all: try lazymatch goal with
    | |- context [getr _ (Z_to_bv 5 (Z.of_nat ?n))] => rewrite (outE n ltac:(lia)); L5K.norm_expr
    end.
  all: try lazymatch goal with
    | |- edenot _ _ = edenot _ _ => apply (BG.edenot_kept 80); [exact agE | reflexivity]
    | |- edenot _ _ = Z_to_bv 64 _ => wordP' num_ok agE
    end.
  all: lazymatch goal with
    | |- ?lo <= bv_unsigned (edenot _ ?e) <= ?hi =>
        rewrite <- (BG.edenot_kept 80 Ein Eout e agE eq_refl); exact (cellsF (KRange e lo hi) ltac:(cbn; tauto))
    end.
Qed.
(* [comment removed for export] *)

End PNADP6.
