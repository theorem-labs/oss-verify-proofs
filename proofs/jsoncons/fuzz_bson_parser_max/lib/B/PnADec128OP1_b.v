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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_adoF_b LibSegBa_adoG1_b LibSegBa_adoG2_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADOP1.
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
Module PadoF := LibSegBa_adoF_b.
Definition KS_adoF_0 : list nat := Eval vm_compute in (BG.kept_list 100 PadoF.regs0 PadoF.regs_out0).
Lemma KS_adoF_0_ok : BG.kept_ok 100 PadoF.regs0 PadoF.regs_out0 KS_adoF_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adoF_1 : list nat := Eval vm_compute in (BG.kept_list 100 PadoF.regs0 PadoF.regs_out1).
Lemma KS_adoF_1_ok : BG.kept_ok 100 PadoF.regs0 PadoF.regs_out1 KS_adoF_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adoF_2 : list nat := Eval vm_compute in (BG.kept_list 100 PadoF.regs0 PadoF.regs_out2).
Lemma KS_adoF_2_ok : BG.kept_ok 100 PadoF.regs0 PadoF.regs_out2 KS_adoF_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adoF_3 : list nat := Eval vm_compute in (BG.kept_list 100 PadoF.regs0 PadoF.regs_out3).
Lemma KS_adoF_3_ok : BG.kept_ok 100 PadoF.regs0 PadoF.regs_out3 KS_adoF_3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adoF_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 16383 -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 13) = Z_to_bv 64 (V 75%nat) -> getr R (reg 17) = Z_to_bv 64 (V 59%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 1 <= (V 75%nat) <= 36 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb4294 M) (st fx' R' 0xb4388 M')
        /\ (forall x, In x KS_adoF_0 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = (((V 75%nat) + 18446744073709551615) mod 2 ^ 64)
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_AND (EVar 59) (ELit 16383))
        /\ getr R' (reg 12) = Z_to_bv 64 18446744073709551610
        /\ bv_unsigned (getr R' (reg 13)) = (V 75%nat)
        /\ getr R' (reg 14) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_AND (EVar 59) (ELit 16383)) (ELit (-6176)))
        /\ bv_unsigned (getr R' (reg 24)) = (((((V 75%nat) + (Z.land (V 59%nat) 16383)) mod 2 ^ 64) + 18446744073709545439) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 75) (EAlu Instr.ALU_AND (EVar 59) (ELit 16383))) (ELit (-6177))) (ELit 18446744073709551610))) <= 1)
      \/ (msteps RSEGS (st fx R 0xb4294 M) (st fx' R' 0xb4388 M')
        /\ (forall x, In x KS_adoF_1 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = (((V 75%nat) + 18446744073709551615) mod 2 ^ 64)
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_AND (EVar 59) (ELit 16383))
        /\ getr R' (reg 12) = Z_to_bv 64 8192
        /\ bv_unsigned (getr R' (reg 13)) = (V 75%nat)
        /\ getr R' (reg 14) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_AND (EVar 59) (ELit 16383)) (ELit (-6176)))
        /\ getr R' (reg 15) = Z_to_bv 64 6177
        /\ bv_unsigned (getr R' (reg 24)) = (((((V 75%nat) + (Z.land (V 59%nat) 16383)) mod 2 ^ 64) + 18446744073709545439) mod 2 ^ 64)
        /\ 6177 <= (Z.land (V 59%nat) 16383)
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 75) (EAlu Instr.ALU_AND (EVar 59) (ELit 16383))) (ELit (-6177))) (ELit 18446744073709551610))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb4294 M) (st fx' R' 0xb44ac M')
        /\ (forall x, In x KS_adoF_2 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = 6176
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_AND (EVar 59) (ELit 16383))
        /\ getr R' (reg 12) = Z_to_bv 64 8192
        /\ bv_unsigned (getr R' (reg 13)) = (V 75%nat)
        /\ getr R' (reg 14) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_AND (EVar 59) (ELit 16383)) (ELit (-6176)))
        /\ getr R' (reg 15) = Z_to_bv 64 6177
        /\ bv_unsigned (getr R' (reg 24)) = (((((V 75%nat) + (Z.land (V 59%nat) 16383)) mod 2 ^ 64) + 18446744073709545439) mod 2 ^ 64)
        /\ 1 <= (((Z.land (V 59%nat) 16383) - 6176) mod 2 ^ 64)
        /\ (Z.land (V 59%nat) 16383) < 6177
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 75) (EAlu Instr.ALU_AND (EVar 59) (ELit 16383))) (ELit (-6177))) (ELit 18446744073709551610))) <= 0)
      \/ (msteps RSEGS (st fx R 0xb4294 M) (st fx' R' 0xb42cc M')
        /\ (forall x, In x KS_adoF_3 -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 10)) = 6176
        /\ getr R' (reg 11) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_AND (EVar 59) (ELit 16383))
        /\ getr R' (reg 12) = Z_to_bv 64 8192
        /\ bv_unsigned (getr R' (reg 13)) = (V 75%nat)
        /\ getr R' (reg 14) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_AND (EVar 59) (ELit 16383)) (ELit (-6176)))
        /\ getr R' (reg 15) = Z_to_bv 64 6177
        /\ getr R' (reg 24) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 75) (EAlu Instr.ALU_AND (EVar 59) (ELit 16383))) (ELit (-6177)))
        /\ getr R' (reg 25) = Z_to_bv 64 0
        /\ (((Z.land (V 59%nat) 16383) - 6176) mod 2 ^ 64) < 1
        /\ (Z.land (V 59%nat) 16383) < 6177
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 59%nat => Z_to_bv 64 (V 59%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 75) (EAlu Instr.ALU_AND (EVar 59) (ELit 16383))) (ELit (-6177))) (ELit 18446744073709551610))) <= 0)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G5 G8 G9 G13 G17 G19 G20 pvzI5 K1 K2 pvzI6.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV59l; move HV59l before pvzI3; pose proof (proj2 pvzI3) as HV59r; move HV59r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV75l; move HV75l before pvzI4; pose proof (proj2 pvzI4) as HV75r; move HV75r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_59 := V 59%nat) in *. set (vz_75 := V 75%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 59%nat => Z_to_bv 64 vz_59 | 75%nat => Z_to_bv 64 vz_75 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 59%nat => vz_59 | 75%nat => vz_75 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 76%nat. }
  assert (HR: regs_ok E PadoF.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadoF.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadoF.kn0).
  { unfold know_ok, PadoF.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadoF.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadoF.NX0 with 100%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadoF.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PadoF.ps0) with 0xb4388 in Hms. change (SR.ps_regs PadoF.ps0) with (map (fun i => (i, nth i PadoF.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoF.ps0) with PadoF.cells0 in Hcells. unfold PadoF.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoF.regs0 PadoF.regs_out0 100 KS_adoF_0 KS_adoF_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoF.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoF.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadoF.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoF.regs_out0]. apply (BG.edenot_kept 100 E E' _ Hag); vm_compute; reflexivity. }
    split. { rewrite (BG.out_reg PadoF.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoF.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoF.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PadoF.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadoF.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PadoF.regs_out0]. apply (BG.edenot_kept 100 E E' _ Hag); vm_compute; reflexivity. }
    split. { rewrite (BG.out_reg PadoF.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadoF.regs_out0]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PadoF.ps1) with 0xb4388 in Hms. change (SR.ps_regs PadoF.ps1) with (map (fun i => (i, nth i PadoF.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoF.ps1) with PadoF.cells1 in Hcells. unfold PadoF.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoF.regs0 PadoF.regs_out1 100 KS_adoF_1 KS_adoF_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoF.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoF.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadoF.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoF.regs_out1]. apply (BG.edenot_kept 100 E E' _ Hag); vm_compute; reflexivity. }
    split. { rewrite (BG.out_reg PadoF.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoF.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PadoF.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadoF.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PadoF.regs_out1]. apply (BG.edenot_kept 100 E E' _ Hag); vm_compute; reflexivity. }
    split. { rewrite (BG.out_reg PadoF.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PadoF.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoF.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PadoF.regs_out1]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. left.
    change (SR.ps_pc PadoF.ps2) with 0xb44ac in Hms. change (SR.ps_regs PadoF.ps2) with (map (fun i => (i, nth i PadoF.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoF.ps2) with PadoF.cells2 in Hcells. unfold PadoF.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoF.regs0 PadoF.regs_out2 100 KS_adoF_2 KS_adoF_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoF.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoF.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadoF.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoF.regs_out2]. apply (BG.edenot_kept 100 E E' _ Hag); vm_compute; reflexivity. }
    split. { rewrite (BG.out_reg PadoF.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoF.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoF.regs_out2 E' R' 13 Hregs) by (clear; lia). cbn [nth PadoF.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadoF.regs_out2 E' R' 14 Hregs) by (clear; lia). cbn [nth PadoF.regs_out2]. apply (BG.edenot_kept 100 E E' _ Hag); vm_compute; reflexivity. }
    split. { rewrite (BG.out_reg PadoF.regs_out2 E' R' 15 Hregs) by (clear; lia). cbn [nth PadoF.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoF.regs_out2 E' R' 24 Hregs) by (clear; lia). cbn [nth PadoF.regs_out2]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right. right.
    change (SR.ps_pc PadoF.ps3) with 0xb42cc in Hms. change (SR.ps_regs PadoF.ps3) with (map (fun i => (i, nth i PadoF.regs_out3 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoF.ps3) with PadoF.cells3 in Hcells. unfold PadoF.cells3 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoF.regs0 PadoF.regs_out3 100 KS_adoF_3 KS_adoF_3_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoF.regs_out3 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoF.regs_out3]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadoF.regs_out3 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoF.regs_out3]. apply (BG.edenot_kept 100 E E' _ Hag); vm_compute; reflexivity. }
    split. { rewrite (BG.out_reg PadoF.regs_out3 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoF.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoF.regs_out3 E' R' 13 Hregs) by (clear; lia). cbn [nth PadoF.regs_out3]. (L5K.evalB' ZA Hag; pvz_unfold ZA). den_tac. }
    split. { rewrite (BG.out_reg PadoF.regs_out3 E' R' 14 Hregs) by (clear; lia). cbn [nth PadoF.regs_out3]. apply (BG.edenot_kept 100 E E' _ Hag); vm_compute; reflexivity. }
    split. { rewrite (BG.out_reg PadoF.regs_out3 E' R' 15 Hregs) by (clear; lia). cbn [nth PadoF.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoF.regs_out3 E' R' 24 Hregs) by (clear; lia). cbn [nth PadoF.regs_out3]. apply (BG.edenot_kept 100 E E' _ Hag); vm_compute; reflexivity. }
    split. { rewrite (BG.out_reg PadoF.regs_out3 E' R' 25 Hregs) by (clear; lia). cbn [nth PadoF.regs_out3]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadoG1 := LibSegBa_adoG1_b.
Definition KS_adoG1 : list nat := Eval vm_compute in (BG.kept_list 100 PadoG1.regs0 PadoG1.regs_out0).
Lemma KS_adoG1_ok : BG.kept_ok 100 PadoG1.regs0 PadoG1.regs_out0 KS_adoG1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adoG1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 13) = Z_to_bv 64 (V 75%nat) -> getr R (reg 18) = Z_to_bv 64 (((V 50%nat) + 32) + (4 * (V 74%nat))) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 30) = Z_to_bv 64 ((V 33%nat) + (V 79%nat)) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  aligned (V 50%nat) 32 -> 4096 <= (V 33%nat) <= 140737488355280 -> aligned (V 33%nat) 8 -> 1 <= (V 75%nat) <= 36 ->
  0 <= (V 79%nat) <= 1 -> 0 <= (V 74%nat) <= 35 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb42cc M) (st fx' R' 0xb430c M')
        /\ (forall x, In x KS_adoG1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 36
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 50%nat) + (4 * (V 74%nat))) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 ((((-1) * (V 50%nat)) + ((-4) * (V 74%nat))) - 33)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 79%nat) + 1)
        /\ getr R' (reg 15) = Z_to_bv 64 2
        /\ getr R' (reg 16) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 17) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 74%nat => Z_to_bv 64 (V 74%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 50)) (EMd Instr.M_MUL (ELit (-4)) (EVar 74))) (ELit (-33))) (ELit 2))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G13 G18 G19 G20 G30 pvzI7 K1 K2 pvzI8 K4 pvzI9 K6 pvzI10 pvzI11 pvzI12.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV50l; move HV50l before pvzI3; pose proof (proj2 pvzI3) as HV50r; move HV50r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV74l; move HV74l before pvzI4; pose proof (proj2 pvzI4) as HV74r; move HV74r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV75l; move HV75l before pvzI5; pose proof (proj2 pvzI5) as HV75r; move HV75r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV79l; move HV79l before pvzI6; pose proof (proj2 pvzI6) as HV79r; move HV79r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K3l; move K3l before pvzI8; pose proof (proj2 pvzI8) as K3r; move K3r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K5l; move K5l before pvzI9; pose proof (proj2 pvzI9) as K5r; move K5r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K7l; move K7l before pvzI10; pose proof (proj2 pvzI10) as K7r; move K7r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K8l; move K8l before pvzI11; pose proof (proj2 pvzI11) as K8r; move K8r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K9l; move K9l before pvzI12; pose proof (proj2 pvzI12) as K9r; move K9r before pvzI12; clear pvzI12.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *. set (vz_79 := V 79%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 50%nat => Z_to_bv 64 vz_50 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | 79%nat => Z_to_bv 64 vz_79 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 50%nat => vz_50 | 74%nat => vz_74 | 75%nat => vz_75 | 79%nat => vz_79 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 80%nat. }
  assert (HR: regs_ok E PadoG1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadoG1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadoG1.kn0).
  { unfold know_ok, PadoG1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r) | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV74l HV74r K9l K9r) | exact (conj K9l K9r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadoG1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadoG1.NX0 with 100%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PadoG1.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PadoG1.ps0) with 0xb430c in Hms. change (SR.ps_regs PadoG1.ps0) with (map (fun i => (i, nth i PadoG1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PadoG1.ps0) with PadoG1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoG1.regs0 PadoG1.regs_out0 100 KS_adoG1 KS_adoG1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PadoG1.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PadoG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoG1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoG1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoG1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoG1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PadoG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoG1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PadoG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoG1.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PadoG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PadoG1.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PadoG1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PadoG1.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PadoG1.regs_out0]. apply (BG.edenot_kept 100 E E' _ Hag); vm_compute; reflexivity.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadoG2 := LibSegBa_adoG2_b.
Definition KS_adoG2_0 : list nat := Eval vm_compute in (BG.kept_list 100 PadoG2.regs0 PadoG2.regs_out0).
Lemma KS_adoG2_0_ok : BG.kept_ok 100 PadoG2.regs0 PadoG2.regs_out0 KS_adoG2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adoG2_1 : list nat := Eval vm_compute in (BG.kept_list 100 PadoG2.regs0 PadoG2.regs_out1).
Lemma KS_adoG2_1_ok : BG.kept_ok 100 PadoG2.regs0 PadoG2.regs_out1 KS_adoG2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adoG2_2 : list nat := Eval vm_compute in (BG.kept_list 100 PadoG2.regs0 PadoG2.regs_out2).
Lemma KS_adoG2_2_ok : BG.kept_ok 100 PadoG2.regs0 PadoG2.regs_out2 KS_adoG2_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adoG2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 -> 0 <= (V 77%nat) < 2 ^ 64 -> 0 <= (V 79%nat) < 2 ^ 64 -> 0 <= (V 80%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 36 -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 77%nat) -> getr R (reg 12) = Z_to_bv 64 (V 76%nat) -> getr R (reg 13) = Z_to_bv 64 0 -> getr R (reg 15) = Z_to_bv 64 2 -> getr R (reg 16) = Z_to_bv 64 (V 75%nat) -> getr R (reg 17) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | 80%nat => Z_to_bv 64 (V 80%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 77)) (EMd Instr.M_MUL (ELit 4) (EVar 76))) (ELit (-1))) (ELit 2)) -> getr R (reg 18) = Z_to_bv 64 (V 77%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 30) = Z_to_bv 64 (V 38%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 77%nat) <= 140737488355320 ->
  aligned (V 77%nat) 4 -> L5KA.zeros_at M (((V 77%nat) / 8) + 2147450880) 1 -> L5.u8_at RSEGS M (V 77%nat) (V 80%nat) -> 0 <= (V 80%nat) <= 9 ->
  (2147446784 + 17592186048512 <= (V 77%nat) \/ (V 77%nat) + 4 <= 2147446784) -> 4096 <= ((V 38%nat) + (V 76%nat)) <= 140737488355321 -> L5KA.zeros_at M ((((V 38%nat) + (V 76%nat)) / 8) + 2147450880) 1 -> L5.writable RSEGS M ((V 38%nat) + (V 76%nat)) 1 ->
  (2147446784 + 17592186048512 <= ((V 38%nat) + (V 76%nat)) \/ ((V 38%nat) + (V 76%nat)) + 1 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= ((V 38%nat) + (V 76%nat)) \/ ((V 38%nat) + (V 76%nat)) + 1 <= ((V 2%nat) - 256)) -> (65536 + 6840320 <= ((V 38%nat) + (V 76%nat)) \/ ((V 38%nat) + (V 76%nat)) + 1 <= 65536) -> (((V 38%nat) + (V 76%nat)) + 1 <= (V 77%nat) \/ (V 77%nat) + 4 <= ((V 38%nat) + (V 76%nat))) ->
  1 <= (V 75%nat) <= 36 -> 0 <= (V 79%nat) <= 1 -> 0 <= (V 76%nat) <= 35 -> 4096 <= (V 38%nat) <= 140737488355280 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 38%nat) + (V 76%nat)) + 0) <= bv_unsigned a < (((V 38%nat) + (V 76%nat)) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 38%nat) + (V 76%nat)) + 0) <= i < (((V 38%nat) + (V 76%nat)) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb430c M) (st fx' R' 0xb430c M')
        /\ (forall x, In x KS_adoG2_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 6) = Z_to_bv 64 ((V 80%nat) + 48)
        /\ getr R' (reg 7) = Z_to_bv 64 0
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 77%nat) + 4)
        /\ getr R' (reg 11) = Z_to_bv 64 ((bv_unsigned (getr R (reg 14))) + (V 76%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 76%nat) + 1)
        /\ getr R' (reg 16) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 17) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | 80%nat => Z_to_bv 64 (V 80%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 77)) (EMd Instr.M_MUL (ELit 4) (EVar 76))) (ELit (-1))) (ELit 2))
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 77%nat) + 4)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 76%nat) + 1)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | 80%nat => Z_to_bv 64 (V 80%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_ADD (EVar 14) (EVar 76)) (ELit 36))) <= 1
        /\ (((V 76%nat) + 1) mod 2 ^ 64) < (V 75%nat)
        /\ L5.u8_at RSEGS M' ((V 38%nat) + (V 76%nat)) ((V 80%nat) + 48))
      \/ (msteps RSEGS (st fx R 0xb430c M) (st fx' R' 0xb46b0 M')
        /\ (forall x, In x KS_adoG2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 6) = Z_to_bv 64 ((V 80%nat) + 48)
        /\ getr R' (reg 7) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 38%nat) + (V 76%nat))
        /\ getr R' (reg 16) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 17) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | 80%nat => Z_to_bv 64 (V 80%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 77)) (EMd Instr.M_MUL (ELit 4) (EVar 76))) (ELit (-1))) (ELit 2))
        /\ getr R' (reg 21) = getr R (reg 21)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 38%nat) + (V 76%nat)) + 1)
        /\ getr R' (reg 25) = Z_to_bv 64 0
        /\ (V 75%nat) <= (((V 76%nat) + 1) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' ((V 38%nat) + (V 76%nat)) ((V 80%nat) + 48))
      \/ (msteps RSEGS (st fx R 0xb430c M) (st fx' R' 0xb46b0 M')
        /\ (forall x, In x KS_adoG2_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 6) = Z_to_bv 64 ((V 80%nat) + 48)
        /\ getr R' (reg 7) = Z_to_bv 64 0
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 77%nat) + 4)
        /\ getr R' (reg 11) = Z_to_bv 64 ((bv_unsigned (getr R (reg 14))) + (V 76%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 76%nat) + 1)
        /\ getr R' (reg 16) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 17) = edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | 80%nat => Z_to_bv 64 (V 80%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-1)) (EVar 77)) (EMd Instr.M_MUL (ELit 4) (EVar 76))) (ELit (-1))) (ELit 2))
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 77%nat) + 4)
        /\ getr R' (reg 21) = getr R (reg 21)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 38%nat) + (V 76%nat)) + 1)
        /\ getr R' (reg 25) = Z_to_bv 64 0
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 75%nat => Z_to_bv 64 (V 75%nat) | 76%nat => Z_to_bv 64 (V 76%nat) | 77%nat => Z_to_bv 64 (V 77%nat) | 79%nat => Z_to_bv 64 (V 79%nat) | 80%nat => Z_to_bv 64 (V 80%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLT (EAlu Instr.ALU_ADD (EVar 14) (EVar 76)) (ELit 36))) <= 0
        /\ (((V 76%nat) + 1) mod 2 ^ 64) < (V 75%nat)
        /\ L5.u8_at RSEGS M' ((V 38%nat) + (V 76%nat)) ((V 80%nat) + 48))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G5 G8 G9 G10 G12 G13 G15 G16 G17 G18 G19 G20 G23 G27 G30 pvzI10 K1 K2 pvzI11 K4 K5 K6 pvzI12 K8 pvzI13 K10 K11 K12 K13 K14 K15 pvzI14 pvzI15 pvzI16 pvzI17.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV38l; move HV38l before pvzI3; pose proof (proj2 pvzI3) as HV38r; move HV38r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV50l; move HV50l before pvzI4; pose proof (proj2 pvzI4) as HV50r; move HV50r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV75l; move HV75l before pvzI5; pose proof (proj2 pvzI5) as HV75r; move HV75r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV76l; move HV76l before pvzI6; pose proof (proj2 pvzI6) as HV76r; move HV76r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV77l; move HV77l before pvzI7; pose proof (proj2 pvzI7) as HV77r; move HV77r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV79l; move HV79l before pvzI8; pose proof (proj2 pvzI8) as HV79r; move HV79r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV80l; move HV80l before pvzI9; pose proof (proj2 pvzI9) as HV80r; move HV80r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K0l; move K0l before pvzI10; pose proof (proj2 pvzI10) as K0r; move K0r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K9l; move K9l before pvzI13; pose proof (proj2 pvzI13) as K9r; move K9r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K16l; move K16l before pvzI14; pose proof (proj2 pvzI14) as K16r; move K16r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K17l; move K17l before pvzI15; pose proof (proj2 pvzI15) as K17r; move K17r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K18l; move K18l before pvzI16; pose proof (proj2 pvzI16) as K18r; move K18r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K19l; move K19l before pvzI17; pose proof (proj2 pvzI17) as K19r; move K19r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_75 := V 75%nat) in *. set (vz_76 := V 76%nat) in *. set (vz_77 := V 77%nat) in *. set (vz_79 := V 79%nat) in *. set (vz_80 := V 80%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 38%nat => Z_to_bv 64 vz_38 | 50%nat => Z_to_bv 64 vz_50 | 75%nat => Z_to_bv 64 vz_75 | 76%nat => Z_to_bv 64 vz_76 | 77%nat => Z_to_bv 64 vz_77 | 79%nat => Z_to_bv 64 vz_79 | 80%nat => Z_to_bv 64 vz_80 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 38%nat => vz_38 | 50%nat => vz_50 | 75%nat => vz_75 | 76%nat => vz_76 | 77%nat => vz_77 | 79%nat => vz_79 | 80%nat => vz_80 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 81%nat. }
  assert (HR: regs_ok E PadoG2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PadoG2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PadoG2.kn0).
  { unfold know_ok, PadoG2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | clear - HV2l HV2r K0l K0r K13; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV77l HV77r K3l K3r K8 K15) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV77l HV77r K3l K3r K8 K15) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV77l HV77r K3l K3r K8 K15) | evalEk ZA ltac:(clear) | clear - HV77l HV77r K3l K3r K8 K15; lia | clear - HV77l HV77r K3l K3r K8 K15; lia | clear - HV77l HV77r K3l K3r K8 K15; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV77l HV77r K3l K3r K8 K15) | evalEk ZA ltac:(clear - HV80l HV80r K7l K7r) | clear - HV77l HV77r K3l K3r K8 K15; lia | clear - HV77l HV77r K3l K3r K8 K15; lia | byte_tac ltac:(clear - HV80l HV80r K7l K7r) | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV80l HV80r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV77l HV77r K3l K3r K8 K15) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r) | exact (conj K9l K9r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r; lia | clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r; lia | clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r) | evalEk ZA ltac:(clear) | clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r; lia | clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r; lia | clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K13) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV77l HV77r K3l K3r K8 K15) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV75l HV75r K16l K16r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV79l HV79r K17l K17r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV76l HV76r K9l K9r K18l K18r K12 K13 K14 K15) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15) | exact (conj K19l K19r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PadoG2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PadoG2.NX0 with 100%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((vz_38 + vz_76) + 0) <= bv_unsigned a < ((vz_38 + vz_76) + 0) + 1) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PadoG2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r) | evalEk' ZA Hag ltac:(clear) | clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PadoG2.ps0) with 0xb430c in Hms. change (SR.ps_regs PadoG2.ps0) with (map (fun i => (i, nth i PadoG2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoG2.ps0) with PadoG2.cells0 in Hcells. unfold PadoG2.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoG2.regs0 PadoG2.regs_out0 100 KS_adoG2_0 KS_adoG2_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoG2.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out0 E' R' 7 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out0]. apply (BG.edenot_kept 100 E E' _ Hag); vm_compute; reflexivity. }
    split. { rewrite (BG.out_reg PadoG2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r) | evalEk' ZA Hag ltac:(clear - HV80l HV80r K7l K7r) | byte_tac ltac:(clear - HV80l HV80r K7l K7r) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PadoG2.ps1) with 0xb46b0 in Hms. change (SR.ps_regs PadoG2.ps1) with (map (fun i => (i, nth i PadoG2.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoG2.ps1) with PadoG2.cells1 in Hcells. unfold PadoG2.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoG2.regs0 PadoG2.regs_out1 100 KS_adoG2_1 KS_adoG2_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoG2.regs_out1 E' R' 6 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out1 E' R' 7 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out1 E' R' 16 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out1 E' R' 17 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out1]. apply (BG.edenot_kept 100 E E' _ Hag); vm_compute; reflexivity. }
    split. { rewrite (BG.out_reg PadoG2.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out1]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadoG2.regs_out1 E' R' 24 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out1 E' R' 25 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r) | evalEk' ZA Hag ltac:(clear - HV80l HV80r K7l K7r) | byte_tac ltac:(clear - HV80l HV80r K7l K7r) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right.
    change (SR.ps_pc PadoG2.ps2) with 0xb46b0 in Hms. change (SR.ps_regs PadoG2.ps2) with (map (fun i => (i, nth i PadoG2.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PadoG2.ps2) with PadoG2.cells2 in Hcells. unfold PadoG2.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PadoG2.regs0 PadoG2.regs_out2 100 KS_adoG2_2 KS_adoG2_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PadoG2.regs_out2 E' R' 6 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out2 E' R' 7 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out2 E' R' 16 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out2 E' R' 17 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out2]. apply (BG.edenot_kept 100 E E' _ Hag); vm_compute; reflexivity. }
    split. { rewrite (BG.out_reg PadoG2.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out2]. rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
    split. { rewrite (BG.out_reg PadoG2.regs_out2 E' R' 23 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out2 E' R' 24 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PadoG2.regs_out2 E' R' 25 Hregs) by (clear; lia). cbn [nth PadoG2.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | rewrite (BG.edenot_kept 100 E E' _ Hag) by (vm_compute; reflexivity); subst E; reflexivity]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); revert HR; clear; intro HR; match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV38l HV38r K9l K9r K19l K19r K12 K13 K14 K15 HV76l HV76r K18l K18r) | evalEk' ZA Hag ltac:(clear - HV80l HV80r K7l K7r) | byte_tac ltac:(clear - HV80l HV80r K7l K7r) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

End PNADOP1.
