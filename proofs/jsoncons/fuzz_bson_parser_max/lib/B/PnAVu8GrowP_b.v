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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3SoundK.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_avsA_b LibSegBa_avsB_b LibSegBa_avsC_b LibSegBa_avaA_b LibSegBa_avaA0_b LibSegBa_avaB_b LibSegBa_avaC_b LibSegBa_avaG_b LibSegBa_avaI_b LibSegBa_avaJ_b LibSegBa_avaBL_b LibSegBa_avaBL1_b LibSegBa_avaGL_b LibSegBa_avaGL1_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMAVGP.
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

Lemma avs_novf (E : env) (a b : nat) :
  bv_unsigned (ev E a) + bv_unsigned (ev E b) < 2 ^ 64 -> bv_unsigned (ev E b) < 2 ^ 63 ->
  bv_unsigned (edenot E (EAlu Instr.ALU_XOR (EAlu Instr.ALU_XOR (EAlu Instr.ALU_SLTU (EVar a) (EAlu Instr.ALU_ADD (EVar a) (EVar b)))
    (EAlu Instr.ALU_SLT (EMd Instr.M_MUL (ELit (-1)) (EVar b)) (ELit 0))) (ELit 1))) = 1.
Proof.
  intros H1 H2.
  pose proof (bv_unsigned_in_range _ (ev E a)) as RA. pose proof (bv_unsigned_in_range _ (ev E b)) as RB.
  change (bv_modulus 64) with (2 ^ 64) in RA, RB.
  cbn [edenot]. rewrite !AX2SK.u_xor64, AX2SK.u_sltu64, AX2SK.u_add64, AX2SK.u_slt64.
  assert (U1 : bv_unsigned (Z_to_bv 64 1) = 1) by reflexivity.
  assert (S0 : bv_signed (Z_to_bv 64 0) = 0) by reflexivity.
  assert (SM : bv_signed (mul_div Instr.M_MUL (Z_to_bv 64 (-1)) (ev E b))
               = (((2 ^ 64 - 1) * bv_unsigned (ev E b)) mod 2 ^ 64 + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63).
  { unfold bv_signed, bv_swrap, bv_wrap. rewrite AX2SK.u_mul64.
    change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
    replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) by reflexivity. reflexivity. }
  rewrite U1, S0, SM.
  set (A := bv_unsigned (ev E a)) in *. set (B := bv_unsigned (ev E b)) in *.
  destruct (Z.eq_dec B 0) as [B0|Bp].
  - assert (L1 : (A <? (A + B) mod 2 ^ 64) = false).
    { rewrite B0, Z.add_0_r, Z.mod_small by lia. apply Z.ltb_ge. lia. }
    assert (L2 : ((((2 ^ 64 - 1) * B) mod 2 ^ 64 + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63 <? 0) = false) by (rewrite B0; reflexivity).
    rewrite L1, L2. reflexivity.
  - assert (L1 : (A <? (A + B) mod 2 ^ 64) = true).
    { rewrite Z.mod_small by lia. apply Z.ltb_lt. lia. }
    assert (L2 : ((((2 ^ 64 - 1) * B) mod 2 ^ 64 + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63 <? 0) = true).
    { replace (((2 ^ 64 - 1) * B) mod 2 ^ 64) with (2 ^ 64 - B) by (apply (Z.mod_unique_pos _ _ (B - 1)); lia).
      replace ((2 ^ 64 - B + 2 ^ 63) mod 2 ^ 64) with (2 ^ 63 - B) by (apply (Z.mod_unique_pos _ _ 1); lia).
      apply Z.ltb_lt. lia. }
    rewrite L1, L2. reflexivity.
Qed.

(* [comment removed for export] *)
Module PavsA := LibSegBa_avsA_b.
Definition KS_avsA : list nat := Eval vm_compute in (BG.kept_list 70 PavsA.regs0 PavsA.regs_out0).
Lemma KS_avsA_ok : BG.kept_ok 70 PavsA.regs0 PavsA.regs_out0 KS_avsA = true. Proof. vm_compute. reflexivity. Qed.
Lemma avsA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 11) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487216 <= (V 2%nat) <= 140737488355280 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 80) + 168 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 80)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 80) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 80) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5cb8 M) (st fx' R' 0xabb8c M')
        /\ (forall x, In x KS_avsA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 744700
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 1309752
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 G2 G10 G11 K0 K1 K2 pvzI3 K4 K5 pvzI4 K7 K8 K9 K10 K11.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as K3l; move K3l before pvzI3; pose proof (proj2 pvzI3) as K3r; move K3r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K6l; move K6l before pvzI4; pose proof (proj2 pvzI4) as K6r; move K6r before pvzI4; clear pvzI4.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 38%nat. }
  assert (HR: regs_ok E PavsA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavsA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavsA.kn0).
  { unfold know_ok, PavsA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavsA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavsA.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 80) <= bv_unsigned a < (vz_2 - 80) + 80) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PavsA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavsA.ps0) with 0xabb8c in Hms. change (SR.ps_regs PavsA.ps0) with (map (fun i => (i, nth i PavsA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavsA.ps0) with PavsA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavsA.regs0 PavsA.regs_out0 70 KS_avsA KS_avsA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavsA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PavsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PavsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PavsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PavsA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavsB := LibSegBa_avsB_b.
Definition KS_avsB : list nat := Eval vm_compute in (BG.kept_list 70 PavsB.regs0 PavsB.regs_out0).
Lemma KS_avsB_ok : BG.kept_ok 70 PavsB.regs0 PavsB.regs_out0 KS_avsB = true. Proof. vm_compute. reflexivity. Qed.
Lemma avsB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487216 <= (V 2%nat) <= 140737488355280 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 80) + 168 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.writable RSEGS M (V 2%nat) 32 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450880) 4 -> L5.u64_at RSEGS M (V 37%nat) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 37%nat) + 8) ((V 40%nat) + (V 41%nat)) -> 0 <= (V 40%nat) <= 140737488355328 -> 0 <= (V 41%nat) <= 134217728 -> L5.u64_at RSEGS M ((V 2%nat) + 8) ((V 44%nat) + (V 41%nat)) ->
  4096 <= (V 44%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) -> (V 44%nat) + (V 41%nat) < 2 ^ 64 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5cfc M) (st fx' R' 0x77c94 M')
        /\ (forall x, In x KS_avsB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 744820
        /\ getr R' (reg 10) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 37%nat) + 8)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) + 8)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 37%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 2%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G2 G8 G9 G21 K0 K1 K2 pvzI16 K4 K5 pvzI17 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 pvzI18 pvzI19 K23 pvzI20 K25 K26 K27 K28 K29 K30.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV49l; move HV49l before pvzI7; pose proof (proj2 pvzI7) as HV49r; move HV49r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV51l; move HV51l before pvzI9; pose proof (proj2 pvzI9) as HV51r; move HV51r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV52l; move HV52l before pvzI10; pose proof (proj2 pvzI10) as HV52r; move HV52r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV53l; move HV53l before pvzI11; pose proof (proj2 pvzI11) as HV53r; move HV53r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV54l; move HV54l before pvzI12; pose proof (proj2 pvzI12) as HV54r; move HV54r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV55l; move HV55l before pvzI13; pose proof (proj2 pvzI13) as HV55r; move HV55r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV56l; move HV56l before pvzI14; pose proof (proj2 pvzI14) as HV56r; move HV56r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV57l; move HV57l before pvzI15; pose proof (proj2 pvzI15) as HV57r; move HV57r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K3l; move K3l before pvzI16; pose proof (proj2 pvzI16) as K3r; move K3r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K6l; move K6l before pvzI17; pose proof (proj2 pvzI17) as K6r; move K6r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K21l; move K21l before pvzI18; pose proof (proj2 pvzI18) as K21r; move K21r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K22l; move K22l before pvzI19; pose proof (proj2 pvzI19) as K22r; move K22r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K24l; move K24l before pvzI20; pose proof (proj2 pvzI20) as K24r; move K24r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 44%nat => Z_to_bv 64 vz_44 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 40%nat => vz_40 | 41%nat => vz_41 | 44%nat => vz_44 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PavsB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavsB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavsB.kn0).
  { unfold know_ok, PavsB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV40l HV40r K21l K21r) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV40l HV40r K21l K21r HV41l HV41r K22l K22r) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K21l K21r) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV41l HV41r K22l K22r HV44l HV44r K24l K24r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [apply (avs_novf E 44%nat 41%nat); rewrite ?ZA; pvz_unfold ZA; cbn beta iota; lia | lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavsB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavsB.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavsB.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavsB.ps0) with 0x77c94 in Hms. change (SR.ps_regs PavsB.ps0) with (map (fun i => (i, nth i PavsB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavsB.ps0) with PavsB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavsB.regs0 PavsB.regs_out0 70 KS_avsB KS_avsB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavsB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PavsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsB.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PavsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PavsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsB.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PavsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsB.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PavsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsB.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PavsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsB.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavsB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavsB.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PavsB.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavsC := LibSegBa_avsC_b.
Definition KS_avsC : list nat := Eval vm_compute in (BG.kept_list 70 PavsC.regs0 PavsC.regs_out0).
Lemma KS_avsC_ok : BG.kept_ok 70 PavsC.regs0 PavsC.regs_out0 KS_avsC = true. Proof. vm_compute. reflexivity. Qed.
Lemma avsC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 (V 37%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 37%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) + 8) -> getr R (reg 20) = Z_to_bv 64 (V 44%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 37%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) + 8) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 37%nat) / 8) + 2147450880) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487216 <= (V 2%nat) <= 140737488355280 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 80 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 80) + 168 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 80)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 51%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 52%nat) -> L5.writable RSEGS M (V 2%nat) 32 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450880) 4 -> L5.u64_at RSEGS M (V 37%nat) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 37%nat) + 8) ((V 40%nat) + (V 41%nat)) -> L5.u64_at RSEGS M ((V 37%nat) + 16) ((V 40%nat) + (V 42%nat)) -> 0 <= (V 40%nat) <= 140737488355328 -> 0 <= (V 41%nat) <= 134217728 ->
  0 <= (V 42%nat) <= 134217728 -> L5.u64_at RSEGS M ((V 2%nat) + 8) ((V 44%nat) + (V 41%nat)) -> L5.u64_at RSEGS M ((V 2%nat) + 16) (((V 44%nat) + (V 41%nat)) + (V 43%nat)) -> L5.u64_at RSEGS M ((V 2%nat) + 24) ((V 44%nat) + (V 46%nat)) ->
  L5.u64_at RSEGS M (V 2%nat) (V 44%nat) -> 4096 <= (V 44%nat) <= 140737488355328 -> 1 <= (V 43%nat) <= 134217728 -> 1 <= (V 46%nat) <= 134217728 ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 56%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 57%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 37%nat) + 0) <= bv_unsigned a < ((V 37%nat) + 0) + 24) -> ~ (((V 2%nat) + 0) <= bv_unsigned a < ((V 2%nat) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 37%nat) + 0) <= i < ((V 37%nat) + 0) + 24) -> ~ (((V 2%nat) + 0) <= i < ((V 2%nat) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5d74 M) (st fx' R' 0xb615c M')
        /\ (forall x, In x KS_avsC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 41%nat) + (V 43%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 56%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 57%nat)
        /\ L5.u64_at RSEGS M' (V 2%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 24) ((V 40%nat) + (V 42%nat))
        /\ L5.u64_at RSEGS M' ((V 37%nat) + 16) ((V 44%nat) + (V 46%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 16) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 37%nat) + 8) (((V 44%nat) + (V 41%nat)) + (V 43%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' (V 37%nat) (V 44%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 G2 G8 G9 G18 G19 G20 G21 G22 G23 G24 K0 K1 K2 pvzI19 K4 K5 pvzI20 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 pvzI21 pvzI22 pvzI23 K25 K26 K27 K28 pvzI24 pvzI25 pvzI26 K32 K33 K34 K35 K36.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV44l; move HV44l before pvzI7; pose proof (proj2 pvzI7) as HV44r; move HV44r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV49l; move HV49l before pvzI10; pose proof (proj2 pvzI10) as HV49r; move HV49r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV50l; move HV50l before pvzI11; pose proof (proj2 pvzI11) as HV50r; move HV50r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV51l; move HV51l before pvzI12; pose proof (proj2 pvzI12) as HV51r; move HV51r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV52l; move HV52l before pvzI13; pose proof (proj2 pvzI13) as HV52r; move HV52r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV53l; move HV53l before pvzI14; pose proof (proj2 pvzI14) as HV53r; move HV53r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV54l; move HV54l before pvzI15; pose proof (proj2 pvzI15) as HV54r; move HV54r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV55l; move HV55l before pvzI16; pose proof (proj2 pvzI16) as HV55r; move HV55r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV56l; move HV56l before pvzI17; pose proof (proj2 pvzI17) as HV56r; move HV56r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV57l; move HV57l before pvzI18; pose proof (proj2 pvzI18) as HV57r; move HV57r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K3l; move K3l before pvzI19; pose proof (proj2 pvzI19) as K3r; move K3r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K6l; move K6l before pvzI20; pose proof (proj2 pvzI20) as K6r; move K6r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K22l; move K22l before pvzI21; pose proof (proj2 pvzI21) as K22r; move K22r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K23l; move K23l before pvzI22; pose proof (proj2 pvzI22) as K23r; move K23r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K24l; move K24l before pvzI23; pose proof (proj2 pvzI23) as K24r; move K24r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K29l; move K29l before pvzI24; pose proof (proj2 pvzI24) as K29r; move K29r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K30l; move K30l before pvzI25; pose proof (proj2 pvzI25) as K30r; move K30r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K31l; move K31l before pvzI26; pose proof (proj2 pvzI26) as K31r; move K31r before pvzI26; clear pvzI26.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 46%nat => Z_to_bv 64 vz_46 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 44%nat => vz_44 | 46%nat => vz_46 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PavsC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavsC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavsC.kn0).
  { unfold know_ok, PavsC.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV40l HV40r K22l K22r) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV40l HV40r K22l K22r HV41l HV41r K23l K23r) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV40l HV40r K22l K22r HV42l HV42r K24l K24r) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV41l HV41r K23l K23r HV44l HV44r K29l K29r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV41l HV41r K23l K23r HV43l HV43r K30l K30r HV44l HV44r K29l K29r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV44l HV44r K29l K29r HV46l HV46r K31l K31r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV44l HV44r K29l K29r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K29l K29r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K30l K30r) | exact (conj K30l K30r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K31l K31r) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV56l HV56r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV57l HV57r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K36]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavsC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavsC.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_37 + 0) <= bv_unsigned a < (vz_37 + 0) + 24) -> ~ ((vz_2 + 0) <= bv_unsigned a < (vz_2 + 0) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PavsC.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavsC.ps0) with 0xb615c in Hms. change (SR.ps_regs PavsC.ps0) with (map (fun i => (i, nth i PavsC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavsC.ps0) with PavsC.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavsC.regs0 PavsC.regs_out0 70 KS_avsC KS_avsC_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavsC.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavsC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsC.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PavsC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsC.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PavsC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsC.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PavsC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsC.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavsC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsC.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavsC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsC.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavsC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsC.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PavsC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsC.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PavsC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsC.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PavsC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsC.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PavsC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsC.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PavsC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsC.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PavsC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavsC.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PavsC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K22l K22r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K22l K22r HV42l HV42r K24l K24r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear - HV44l HV44r K29l K29r HV46l HV46r K31l K31r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K22l K22r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K23l K23r HV43l HV43r K30l K30r HV44l HV44r K29l K29r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K22l K22r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear - HV44l HV44r K29l K29r) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavaA := LibSegBa_avaA_b.
Definition KS_avaA_0 : list nat := Eval vm_compute in (BG.kept_list 70 PavaA.regs0 PavaA.regs_out0).
Lemma KS_avaA_0_ok : BG.kept_ok 70 PavaA.regs0 PavaA.regs_out0 KS_avaA_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avaA_1 : list nat := Eval vm_compute in (BG.kept_list 70 PavaA.regs0 PavaA.regs_out1).
Lemma KS_avaA_1_ok : BG.kept_ok 70 PavaA.regs0 PavaA.regs_out1 KS_avaA_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avaA_2 : list nat := Eval vm_compute in (BG.kept_list 70 PavaA.regs0 PavaA.regs_out2).
Lemma KS_avaA_2_ok : BG.kept_ok 70 PavaA.regs0 PavaA.regs_out2 KS_avaA_2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avaA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 11) = Z_to_bv 64 (V 43%nat) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 128)) ->
  L5.u64_at RSEGS M (V 37%nat) (V 40%nat) -> L5.u64_at RSEGS M ((V 37%nat) + 8) ((V 40%nat) + (V 41%nat)) -> L5.u64_at RSEGS M ((V 37%nat) + 16) ((V 40%nat) + (V 42%nat)) -> 0 <= (V 41%nat) <= 134217728 ->
  1 <= (V 42%nat) <= 134217728 -> 0 <= (((-1) * (V 41%nat)) + (V 42%nat)) <= 134217728 -> 1 <= (V 43%nat) <= 134217728 -> 4096 <= (V 40%nat) <= 140737488355328 ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5800 M) (st fx' R' 0xb609c M')
        /\ (forall x, In x KS_avaA_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 743960
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 8) = Z_to_bv 64 2147450880
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 40%nat) + (V 41%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ (V 43%nat) <= ((((18446744073709551615 * (V 41%nat)) mod 2 ^ 64) + (V 42%nat)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb5800 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_avaA_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 744192
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 40)
        /\ getr R' (reg 9) = Z_to_bv 64 (2 * (V 42%nat))
        /\ getr R' (reg 10) = Z_to_bv 64 (2 * (V 42%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 4611686018427387903
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 40) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 743592
        /\ ((V 41%nat) + (V 43%nat)) < (2 * (V 42%nat))
        /\ ((((18446744073709551615 * (V 41%nat)) mod 2 ^ 64) + (V 42%nat)) mod 2 ^ 64) < (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))
      \/ (msteps RSEGS (st fx R 0xb5800 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_avaA_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 744192
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 40)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 41%nat) + (V 43%nat))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 41%nat) + (V 43%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 4611686018427387903
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 40) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 743592
        /\ (2 * (V 42%nat)) <= ((V 41%nat) + (V 43%nat))
        /\ ((((18446744073709551615 * (V 41%nat)) mod 2 ^ 64) + (V 42%nat)) mod 2 ^ 64) < (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1))))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G10 G11 K0 K1 K2 pvzI7 K4 K5 pvzI8 K7 K8 K9 K10 K11 K12 K13 K14 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 K20.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K3l; move K3l before pvzI7; pose proof (proj2 pvzI7) as K3r; move K3r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K6l; move K6l before pvzI8; pose proof (proj2 pvzI8) as K6r; move K6r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K15l; move K15l before pvzI9; pose proof (proj2 pvzI9) as K15r; move K15r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K16l; move K16l before pvzI10; pose proof (proj2 pvzI10) as K16r; move K16r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K17l; move K17l before pvzI11; pose proof (proj2 pvzI11) as K17r; move K17r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K18l; move K18l before pvzI12; pose proof (proj2 pvzI12) as K18r; move K18r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K19l; move K19l before pvzI13; pose proof (proj2 pvzI13) as K19r; move K19r before pvzI13; clear pvzI13.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PavaA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavaA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavaA.kn0).
  { unfold know_ok, PavaA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r HV41l HV41r K15l K15r K17l K17r) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV40l HV40r K19l K19r HV42l HV42r K16l K16r K17l K17r) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K15l K15r K17l K17r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K16l K16r K17l K17r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K15l K15r K17l K17r HV42l HV42r K16l K16r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K18l K18r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K20]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavaA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavaA.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PavaA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PavaA.ps0) with 0xb609c in Hms. change (SR.ps_regs PavaA.ps0) with (map (fun i => (i, nth i PavaA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavaA.ps0) with PavaA.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaA.regs0 PavaA.regs_out0 70 KS_avaA_0 KS_avaA_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavaA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PavaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PavaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PavaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r HV41l HV41r K15l K15r K17l K17r HV43l HV43r K18l K18r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K19l K19r HV41l HV41r K15l K15r K17l K17r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end).
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. left.
    change (SR.ps_pc PavaA.ps1) with 0x130338 in Hms. change (SR.ps_regs PavaA.ps1) with (map (fun i => (i, nth i PavaA.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavaA.ps1) with PavaA.cells1 in Hcells. unfold PavaA.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaA.regs0 PavaA.regs_out1 70 KS_avaA_1 KS_avaA_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavaA.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PavaA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PavaA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PavaA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PavaA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavaA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavaA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PavaA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PavaA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out1 E' R' 18 Hregs) by (clear; lia). cbn [nth PavaA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out1 E' R' 19 Hregs) by (clear; lia). cbn [nth PavaA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out1 E' R' 20 Hregs) by (clear; lia). cbn [nth PavaA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out1 E' R' 21 Hregs) by (clear; lia). cbn [nth PavaA.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K18l K18r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right. right.
    change (SR.ps_pc PavaA.ps2) with 0x130338 in Hms. change (SR.ps_regs PavaA.ps2) with (map (fun i => (i, nth i PavaA.regs_out2 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavaA.ps2) with PavaA.cells2 in Hcells. unfold PavaA.cells2 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaA.regs0 PavaA.regs_out2 70 KS_avaA_2 KS_avaA_2_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavaA.regs_out2 E' R' 1 Hregs) by (clear; lia). cbn [nth PavaA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out2 E' R' 2 Hregs) by (clear; lia). cbn [nth PavaA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out2 E' R' 8 Hregs) by (clear; lia). cbn [nth PavaA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out2 E' R' 9 Hregs) by (clear; lia). cbn [nth PavaA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out2 E' R' 10 Hregs) by (clear; lia). cbn [nth PavaA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out2 E' R' 11 Hregs) by (clear; lia). cbn [nth PavaA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out2 E' R' 12 Hregs) by (clear; lia). cbn [nth PavaA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out2 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out2 E' R' 14 Hregs) by (clear; lia). cbn [nth PavaA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out2 E' R' 18 Hregs) by (clear; lia). cbn [nth PavaA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out2 E' R' 19 Hregs) by (clear; lia). cbn [nth PavaA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out2 E' R' 20 Hregs) by (clear; lia). cbn [nth PavaA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaA.regs_out2 E' R' 21 Hregs) by (clear; lia). cbn [nth PavaA.regs_out2]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K18l K18r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavaA0 := LibSegBa_avaA0_b.
Definition KS_avaA0 : list nat := Eval vm_compute in (BG.kept_list 70 PavaA0.regs0 PavaA0.regs_out0).
Lemma KS_avaA0_ok : BG.kept_ok 70 PavaA0.regs0 PavaA0.regs_out0 KS_avaA0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avaA0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 37%nat) -> getr R (reg 11) = Z_to_bv 64 (V 43%nat) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 128)) ->
  L5.u64_at RSEGS M (V 37%nat) 0 -> L5.u64_at RSEGS M ((V 37%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 37%nat) + 16) 0 -> 1 <= (V 43%nat) <= 134217728 ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5800 M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_avaA0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 744192
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 40)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 4611686018427387903
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 40) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 743592
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros pvzI1 pvzI2 pvzI3 G2 G10 G11 K0 K1 K2 pvzI4 K4 K5 pvzI5 K7 K8 K9 K10 K11 K12 K13 K14 pvzI6 K16.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV43l; move HV43l before pvzI3; pose proof (proj2 pvzI3) as HV43r; move HV43r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as K3l; move K3l before pvzI4; pose proof (proj2 pvzI4) as K3r; move K3r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K6l; move K6l before pvzI5; pose proof (proj2 pvzI5) as K6r; move K6r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K15l; move K15l before pvzI6; pose proof (proj2 pvzI6) as K15r; move K15r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_43 := V 43%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 43%nat => Z_to_bv 64 vz_43 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 43%nat => vz_43 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PavaA0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavaA0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavaA0.kn0).
  { unfold know_ok, PavaA0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K16]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavaA0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavaA0.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PavaA0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavaA0.ps0) with 0x130338 in Hms. change (SR.ps_regs PavaA0.ps0) with (map (fun i => (i, nth i PavaA0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavaA0.ps0) with PavaA0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaA0.regs0 PavaA0.regs_out0 70 KS_avaA0 KS_avaA0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavaA0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaA0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PavaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaA0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PavaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaA0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PavaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaA0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaA0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaA0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaA0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaA0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PavaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaA0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PavaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaA0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PavaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaA0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PavaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaA0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PavaA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K15l K15r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavaB := LibSegBa_avaB_b.
Definition KS_avaB : list nat := Eval vm_compute in (BG.kept_list 70 PavaB.regs0 PavaB.regs_out0).
Lemma KS_avaB_ok : BG.kept_ok 70 PavaB.regs0 PavaB.regs_out0 KS_avaB = true. Proof. vm_compute. reflexivity. Qed.
Lemma avaB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 2147450880 -> getr R (reg 9) = Z_to_bv 64 ((V 40%nat) + ((V 41%nat) + (V 43%nat))) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 128)) ->
  1 <= (V 43%nat) <= 134217728 -> 4096 <= (V 40%nat) <= 140737488355328 -> 0 <= (V 41%nat) <= 134217728 -> L5.writable RSEGS M (V 40%nat) (V 42%nat) ->
  1 <= (V 42%nat) <= 134217728 -> 1 <= (((-1) * (V 41%nat)) + (V 42%nat)) <= 134217728 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat))) -> L5.u64_at RSEGS M ((V 2%nat) - 40) ((V 40%nat) + (V 41%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 37%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5a18 M) (st fx' R' 0xb5a34 M')
        /\ (forall x, In x KS_avaB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + (V 41%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + (V 41%nat))
        /\ getr R' (reg 12) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 13) = Z_to_bv 64 ((((V 40%nat) + (V 41%nat)) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 40%nat) + (V 41%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 pvzI12 pvzI13 pvzI14 K15 pvzI15 pvzI16 K18 K19 K20 K21 K22 K23 K24.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV49l; move HV49l before pvzI8; pose proof (proj2 pvzI8) as HV49r; move HV49r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K12l; move K12l before pvzI12; pose proof (proj2 pvzI12) as K12r; move K12r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K13l; move K13l before pvzI13; pose proof (proj2 pvzI13) as K13r; move K13r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K14l; move K14l before pvzI14; pose proof (proj2 pvzI14) as K14r; move K14r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K16l; move K16l before pvzI15; pose proof (proj2 pvzI15) as K16r; move K16r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K17l; move K17l before pvzI16; pose proof (proj2 pvzI16) as K17r; move K17r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PavaB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavaB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavaB.kn0).
  { unfold know_ok, PavaB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K17l K17r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K13l K13r) | evalEk ZA ltac:(clear - HV42l HV42r K16l K16r K17l K17r) | clear - HV40l HV40r K13l K13r HV42l HV42r K16l K16r K17l K17r; lia | clear - HV40l HV40r K13l K13r HV42l HV42r K16l K16r K17l K17r; lia | clear - HV40l HV40r K13l K13r HV42l HV42r K16l K16r K17l K17r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K16l K16r K17l K17r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K17l K17r HV42l HV42r K16l K16r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r HV41l HV41r K14l K14r K17l K17r HV43l HV43r K12l K12r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r HV41l HV41r K14l K14r K17l K17r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K24]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavaB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavaB.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PavaB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavaB.ps0) with 0xb5a34 in Hms. change (SR.ps_regs PavaB.ps0) with (map (fun i => (i, nth i PavaB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavaB.ps0) with PavaB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaB.regs0 PavaB.regs_out0 70 KS_avaB KS_avaB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavaB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r HV41l HV41r K14l K14r K17l K17r HV43l HV43r K12l K12r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r HV41l HV41r K14l K14r K17l K17r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia].
Qed.
(* [comment removed for export] *)

Module PavaBL := LibSegBa_avaBL_b.
Definition KS_avaBL_0 : list nat := Eval vm_compute in (BG.kept_list 57 PavaBL.regs0 PavaBL.regs_out0).
Lemma KS_avaBL_0_ok : BG.kept_ok 57 PavaBL.regs0 PavaBL.regs_out0 KS_avaBL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avaBL_1 : list nat := Eval vm_compute in (BG.kept_list 57 PavaBL.regs0 PavaBL.regs_out1).
Lemma KS_avaBL_1_ok : BG.kept_ok 57 PavaBL.regs0 PavaBL.regs_out1 KS_avaBL_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avaBL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 2147450880 -> getr R (reg 9) = Z_to_bv 64 ((V 40%nat) + ((V 41%nat) + (V 43%nat))) -> getr R (reg 10) = Z_to_bv 64 ((V 40%nat) + (V 56%nat)) -> getr R (reg 11) = Z_to_bv 64 ((V 40%nat) + (V 56%nat)) -> getr R (reg 12) = Z_to_bv 64 18446744073709551615 -> getr R (reg 13) = Z_to_bv 64 ((((V 40%nat) + (V 56%nat)) / 8) + 2147450880) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 128)) ->
  1 <= (V 43%nat) <= 134217728 -> 4096 <= (V 40%nat) <= 140737488355328 -> 0 <= (V 41%nat) <= 134217728 -> L5.writable RSEGS M (V 40%nat) (V 42%nat) ->
  (((V 2%nat) - 128) + 128 <= (V 40%nat) \/ (V 40%nat) + (V 42%nat) <= ((V 2%nat) - 128)) -> 1 <= (V 42%nat) <= 134217728 -> 1 <= (((-1) * (V 41%nat)) + (V 42%nat)) <= 134217728 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat))) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) ((V 40%nat) + (V 56%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 37%nat) -> 0 <= (V 56%nat) <= 134217728 -> 0 <= (((-1) * (V 41%nat)) + (V 56%nat)) <= 134217728 ->
  1 <= (((-1) * (V 56%nat)) + ((V 41%nat) + (V 43%nat))) <= 134217728 -> 1 <= (((-1) * (V 56%nat)) + (V 42%nat)) <= 134217728 -> L5.u8_at RSEGS M ((((V 40%nat) + (V 56%nat)) / 8) + 2147450880) (V 55%nat) -> 0 <= (V 55%nat) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ ((((V 40%nat) + (V 56%nat)) + 0) <= bv_unsigned a < (((V 40%nat) + (V 56%nat)) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> ~ ((((V 40%nat) + (V 56%nat)) + 0) <= i < (((V 40%nat) + (V 56%nat)) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5a34 M) (st fx' R' 0xb5fbc M')
        /\ (forall x, In x KS_avaBL_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 744044
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 40%nat) + (V 56%nat)) + 1)
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ (((((((V 40%nat) + (V 56%nat)) mod 2 ^ 64) + 1) mod 2 ^ 64) - (((V 40%nat) + (((V 41%nat) + (V 43%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (((V 40%nat) + (V 56%nat)) + 1)
        /\ L5.u8_at RSEGS M' ((V 40%nat) + (V 56%nat)) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 37%nat))
      \/ (msteps RSEGS (st fx R 0xb5a34 M) (st fx' R' 0xb5a34 M')
        /\ (forall x, In x KS_avaBL_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 40%nat) + (V 56%nat)) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 40%nat) + (V 56%nat)) + 1)
        /\ getr R' (reg 13) = Z_to_bv 64 (((((V 40%nat) + (V 56%nat)) + 1) / 8) + 2147450880)
        /\ 1 <= (((((((V 40%nat) + (V 56%nat)) mod 2 ^ 64) + 1) mod 2 ^ 64) - (((V 40%nat) + (((V 41%nat) + (V 43%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (((V 40%nat) + (V 56%nat)) + 1)
        /\ L5.u8_at RSEGS M' ((V 40%nat) + (V 56%nat)) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 37%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G10 G11 G12 G13 K0 K1 K2 pvzI12 K4 K5 pvzI13 K7 K8 K9 K10 K11 pvzI14 pvzI15 pvzI16 K15 K16 pvzI17 pvzI18 K19 K20 K21 K22 K23 K24 K25 pvzI19 pvzI20 pvzI21 pvzI22 K30 pvzI23.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV49l; move HV49l before pvzI8; pose proof (proj2 pvzI8) as HV49r; move HV49r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV55l; move HV55l before pvzI10; pose proof (proj2 pvzI10) as HV55r; move HV55r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV56l; move HV56l before pvzI11; pose proof (proj2 pvzI11) as HV56r; move HV56r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K3l; move K3l before pvzI12; pose proof (proj2 pvzI12) as K3r; move K3r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K6l; move K6l before pvzI13; pose proof (proj2 pvzI13) as K6r; move K6r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K12l; move K12l before pvzI14; pose proof (proj2 pvzI14) as K12r; move K12r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K13l; move K13l before pvzI15; pose proof (proj2 pvzI15) as K13r; move K13r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K14l; move K14l before pvzI16; pose proof (proj2 pvzI16) as K14r; move K14r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K17l; move K17l before pvzI17; pose proof (proj2 pvzI17) as K17r; move K17r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K18l; move K18l before pvzI18; pose proof (proj2 pvzI18) as K18r; move K18r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K27l; move K27l before pvzI20; pose proof (proj2 pvzI20) as K27r; move K27r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K28l; move K28l before pvzI21; pose proof (proj2 pvzI21) as K28r; move K28r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K29l; move K29l before pvzI22; pose proof (proj2 pvzI22) as K29r; move K29r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K31l; move K31l before pvzI23; pose proof (proj2 pvzI23) as K31r; move K31r before pvzI23; clear pvzI23.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 55%nat => vz_55 | 56%nat => vz_56 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PavaBL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavaBL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavaBL.kn0).
  { unfold know_ok, PavaBL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K12l K12r K28l K28r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K13l K13r K16) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K18l K18r K27l K27r K28l K28r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K13l K13r K16) | evalEk ZA ltac:(clear - HV42l HV42r K17l K17r K18l K18r K29l K29r) | clear - HV40l HV40r K13l K13r K16 HV42l HV42r K17l K17r K18l K18r K29l K29r; lia | clear - HV40l HV40r K13l K13r K16 HV42l HV42r K17l K17r K18l K18r K29l K29r; lia | clear - HV40l HV40r K13l K13r K16 HV42l HV42r K17l K17r K18l K18r K29l K29r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r K16) | evalEk ZA ltac:(clear - HV42l HV42r K17l K17r K18l K18r K29l K29r) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K17l K17r K18l K18r K29l K29r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K18l K18r K27l K27r K28l K28r HV42l HV42r K17l K17r K29l K29r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r K16 HV41l HV41r K14l K14r K18l K18r K27l K27r K28l K28r HV43l HV43r K12l K12r) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K18l K18r K27l K27r K28l K28r HV56l HV56r K26l K26r K29l K29r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K18l K18r K27l K27r K28l K28r HV43l HV43r K12l K12r HV56l HV56r K26l K26r K29l K29r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K17l K17r K18l K18r K29l K29r HV56l HV56r K26l K26r K27l K27r K28l K28r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K13l K13r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r) | evalEk ZA ltac:(clear - HV55l HV55r K31l K31r) | clear - HV40l HV40r K13l K13r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r; lia | clear - HV40l HV40r K13l K13r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r; lia | byte_tac ltac:(clear - HV55l HV55r K31l K31r) | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K31l K31r) | exact (conj K31l K31r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavaBL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavaBL.NX0 with 57%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> ~ (((vz_40 + vz_56) + 0) <= bv_unsigned a < ((vz_40 + vz_56) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PavaBL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K13l K13r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PavaBL.ps0) with 0xb5fbc in Hms. change (SR.ps_regs PavaBL.ps0) with (map (fun i => (i, nth i PavaBL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavaBL.ps0) with PavaBL.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaBL.regs0 PavaBL.regs_out0 57 KS_avaBL_0 KS_avaBL_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavaBL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavaBL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaBL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavaBL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaBL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavaBL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaBL.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaBL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r K16 HV41l HV41r K14l K14r K18l K18r K27l K27r K28l K28r HV43l HV43r K12l K12r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right.
    change (SR.ps_pc PavaBL.ps1) with 0xb5a34 in Hms. change (SR.ps_regs PavaBL.ps1) with (map (fun i => (i, nth i PavaBL.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavaBL.ps1) with PavaBL.cells1 in Hcells. unfold PavaBL.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaBL.regs0 PavaBL.regs_out1 57 KS_avaBL_1 KS_avaBL_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavaBL.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavaBL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaBL.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavaBL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaBL.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaBL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r K16 HV41l HV41r K14l K14r K18l K18r K27l K27r K28l K28r HV43l HV43r K12l K12r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module PavaBL1 := LibSegBa_avaBL1_b.
Definition KS_avaBL1_0 : list nat := Eval vm_compute in (BG.kept_list 57 PavaBL1.regs0 PavaBL1.regs_out0).
Lemma KS_avaBL1_0_ok : BG.kept_ok 57 PavaBL1.regs0 PavaBL1.regs_out0 KS_avaBL1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avaBL1_1 : list nat := Eval vm_compute in (BG.kept_list 57 PavaBL1.regs0 PavaBL1.regs_out1).
Lemma KS_avaBL1_1_ok : BG.kept_ok 57 PavaBL1.regs0 PavaBL1.regs_out1 KS_avaBL1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avaBL1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 2147450880 -> getr R (reg 9) = Z_to_bv 64 ((V 40%nat) + ((V 41%nat) + (V 43%nat))) -> getr R (reg 10) = Z_to_bv 64 ((V 40%nat) + (V 56%nat)) -> getr R (reg 11) = Z_to_bv 64 ((V 40%nat) + (V 56%nat)) -> getr R (reg 12) = Z_to_bv 64 18446744073709551615 -> getr R (reg 13) = Z_to_bv 64 ((((V 40%nat) + (V 56%nat)) / 8) + 2147450880) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 128)) ->
  1 <= (V 43%nat) <= 134217728 -> 4096 <= (V 40%nat) <= 140737488355328 -> 0 <= (V 41%nat) <= 134217728 -> L5.writable RSEGS M (V 40%nat) (V 42%nat) ->
  (((V 2%nat) - 128) + 128 <= (V 40%nat) \/ (V 40%nat) + (V 42%nat) <= ((V 2%nat) - 128)) -> 1 <= (V 42%nat) <= 134217728 -> 1 <= (((-1) * (V 41%nat)) + (V 42%nat)) <= 134217728 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat))) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) ((V 40%nat) + (V 56%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 37%nat) -> 0 <= (V 56%nat) <= 134217728 -> 0 <= (((-1) * (V 41%nat)) + (V 56%nat)) <= 134217728 ->
  1 <= (((-1) * (V 56%nat)) + ((V 41%nat) + (V 43%nat))) <= 134217728 -> 1 <= (((-1) * (V 56%nat)) + (V 42%nat)) <= 134217728 -> L5.u8_at RSEGS M ((((V 40%nat) + (V 56%nat)) / 8) + 2147450880) (V 55%nat) -> 1 <= (V 55%nat) <= 7 ->
  1 <= ((V 55%nat) - (Z.land ((V 40%nat) + (V 56%nat)) 7)) <= 7 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ ((((V 40%nat) + (V 56%nat)) + 0) <= bv_unsigned a < (((V 40%nat) + (V 56%nat)) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> ~ ((((V 40%nat) + (V 56%nat)) + 0) <= i < (((V 40%nat) + (V 56%nat)) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5a34 M) (st fx' R' 0xb5fbc M')
        /\ (forall x, In x KS_avaBL1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 744044
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 40%nat) + (V 56%nat)) + 1)
        /\ getr R' (reg 13) = Z_to_bv 64 (V 55%nat)
        /\ (((((((V 40%nat) + (V 56%nat)) mod 2 ^ 64) + 1) mod 2 ^ 64) - (((V 40%nat) + (((V 41%nat) + (V 43%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (((V 40%nat) + (V 56%nat)) + 1)
        /\ L5.u8_at RSEGS M' ((V 40%nat) + (V 56%nat)) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 37%nat))
      \/ (msteps RSEGS (st fx R 0xb5a34 M) (st fx' R' 0xb5a34 M')
        /\ (forall x, In x KS_avaBL1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 40%nat) + (V 56%nat)) + 1)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 40%nat) + (V 56%nat)) + 1)
        /\ getr R' (reg 13) = Z_to_bv 64 (((((V 40%nat) + (V 56%nat)) + 1) / 8) + 2147450880)
        /\ 1 <= (((((((V 40%nat) + (V 56%nat)) mod 2 ^ 64) + 1) mod 2 ^ 64) - (((V 40%nat) + (((V 41%nat) + (V 43%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (((V 40%nat) + (V 56%nat)) + 1)
        /\ L5.u8_at RSEGS M' ((V 40%nat) + (V 56%nat)) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 37%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G10 G11 G12 G13 K0 K1 K2 pvzI12 K4 K5 pvzI13 K7 K8 K9 K10 K11 pvzI14 pvzI15 pvzI16 K15 K16 pvzI17 pvzI18 K19 K20 K21 K22 K23 K24 K25 pvzI19 pvzI20 pvzI21 pvzI22 K30 pvzI23 pvzI24.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV49l; move HV49l before pvzI8; pose proof (proj2 pvzI8) as HV49r; move HV49r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV55l; move HV55l before pvzI10; pose proof (proj2 pvzI10) as HV55r; move HV55r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV56l; move HV56l before pvzI11; pose proof (proj2 pvzI11) as HV56r; move HV56r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K3l; move K3l before pvzI12; pose proof (proj2 pvzI12) as K3r; move K3r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K6l; move K6l before pvzI13; pose proof (proj2 pvzI13) as K6r; move K6r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K12l; move K12l before pvzI14; pose proof (proj2 pvzI14) as K12r; move K12r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K13l; move K13l before pvzI15; pose proof (proj2 pvzI15) as K13r; move K13r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K14l; move K14l before pvzI16; pose proof (proj2 pvzI16) as K14r; move K14r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K17l; move K17l before pvzI17; pose proof (proj2 pvzI17) as K17r; move K17r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K18l; move K18l before pvzI18; pose proof (proj2 pvzI18) as K18r; move K18r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K26l; move K26l before pvzI19; pose proof (proj2 pvzI19) as K26r; move K26r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K27l; move K27l before pvzI20; pose proof (proj2 pvzI20) as K27r; move K27r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K28l; move K28l before pvzI21; pose proof (proj2 pvzI21) as K28r; move K28r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K29l; move K29l before pvzI22; pose proof (proj2 pvzI22) as K29r; move K29r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K31l; move K31l before pvzI23; pose proof (proj2 pvzI23) as K31r; move K31r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K32l; move K32l before pvzI24; pose proof (proj2 pvzI24) as K32r; move K32r before pvzI24; clear pvzI24.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 55%nat => vz_55 | 56%nat => vz_56 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PavaBL1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavaBL1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavaBL1.kn0).
  { unfold know_ok, PavaBL1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K12l K12r K28l K28r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K13l K13r K32l K32r K16) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K18l K18r K27l K27r K28l K28r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K13l K13r K32l K32r K16) | evalEk ZA ltac:(clear - HV42l HV42r K17l K17r K18l K18r K29l K29r) | clear - HV40l HV40r K13l K13r K32l K32r K16 HV42l HV42r K17l K17r K18l K18r K29l K29r; lia | clear - HV40l HV40r K13l K13r K32l K32r K16 HV42l HV42r K17l K17r K18l K18r K29l K29r; lia | clear - HV40l HV40r K13l K13r K32l K32r K16 HV42l HV42r K17l K17r K18l K18r K29l K29r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r K32l K32r K16) | evalEk ZA ltac:(clear - HV42l HV42r K17l K17r K18l K18r K29l K29r) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K17l K17r K18l K18r K29l K29r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K18l K18r K27l K27r K28l K28r HV42l HV42r K17l K17r K29l K29r) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r K32l K32r K16 HV41l HV41r K14l K14r K18l K18r K27l K27r K28l K28r HV43l HV43r K12l K12r) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r K32l K32r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear - HV2l HV2r K3l K3r K11 K16; lia | clear - HV2l HV2r K3l K3r K11 K16; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r K32l K32r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K18l K18r K27l K27r K28l K28r HV56l HV56r K26l K26r K29l K29r K32l K32r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K18l K18r K27l K27r K28l K28r HV43l HV43r K12l K12r HV56l HV56r K26l K26r K29l K29r K32l K32r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K17l K17r K18l K18r K29l K29r HV56l HV56r K26l K26r K27l K27r K28l K28r K32l K32r) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV40l HV40r K13l K13r K32l K32r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r) | evalEk ZA ltac:(clear - HV55l HV55r K31l K31r K32l K32r) | clear - HV40l HV40r K13l K13r K32l K32r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r; lia | clear - HV40l HV40r K13l K13r K32l K32r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r; lia | byte_tac ltac:(clear - HV55l HV55r K31l K31r K32l K32r) | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K31l K31r K32l K32r) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | repeat match goal with |- context [Z.land (?x mod 2 ^ 64) ?k] => rewrite (Z.mod_small x (2 ^ 64)) by lia end; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavaBL1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavaBL1.NX0 with 57%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> ~ (((vz_40 + vz_56) + 0) <= bv_unsigned a < ((vz_40 + vz_56) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PavaBL1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r K32l K32r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K13l K13r K32l K32r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PavaBL1.ps0) with 0xb5fbc in Hms. change (SR.ps_regs PavaBL1.ps0) with (map (fun i => (i, nth i PavaBL1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavaBL1.ps0) with PavaBL1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaBL1.regs0 PavaBL1.regs_out0 57 KS_avaBL1_0 KS_avaBL1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavaBL1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavaBL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaBL1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavaBL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaBL1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavaBL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaBL1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaBL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r K32l K32r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r K32l K32r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r K32l K32r K16 HV41l HV41r K14l K14r K18l K18r K27l K27r K28l K28r HV43l HV43r K12l K12r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right.
    change (SR.ps_pc PavaBL1.ps1) with 0xb5a34 in Hms. change (SR.ps_regs PavaBL1.ps1) with (map (fun i => (i, nth i PavaBL1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavaBL1.ps1) with PavaBL1.cells1 in Hcells. unfold PavaBL1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaBL1.regs0 PavaBL1.regs_out1 57 KS_avaBL1_1 KS_avaBL1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavaBL1.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavaBL1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaBL1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavaBL1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaBL1.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaBL1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r K32l K32r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r) | clear; lia]. }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r K32l K32r K16 HV56l HV56r K26l K26r K27l K27r K28l K28r K29l K29r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r K32l K32r K16 HV41l HV41r K14l K14r K18l K18r K27l K27r K28l K28r HV43l HV43r K12l K12r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K16) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

(* [comment removed for export] *)
Module PavaC := LibSegBa_avaC_b.
Definition KS_avaC : list nat := Eval vm_compute in (BG.kept_list 70 PavaC.regs0 PavaC.regs_out0).
Lemma KS_avaC_ok : BG.kept_ok 70 PavaC.regs0 PavaC.regs_out0 KS_avaC = true. Proof. vm_compute. reflexivity. Qed.
Lemma avaC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 744044 -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 8) = Z_to_bv 64 2147450880 -> getr R (reg 9) = Z_to_bv 64 ((V 40%nat) + ((V 41%nat) + (V 43%nat))) -> getr R (reg 10) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 11) = Z_to_bv 64 ((V 40%nat) + ((V 41%nat) + (V 43%nat))) -> getr R (reg 12) = Z_to_bv 64 18446744073709551615 ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 128)) ->
  1 <= (V 43%nat) <= 134217728 -> 4096 <= (V 40%nat) <= 140737488355328 -> 0 <= (V 41%nat) <= 134217728 -> L5.writable RSEGS M (V 40%nat) (V 42%nat) ->
  1 <= (V 42%nat) <= 134217728 -> 1 <= (((-1) * (V 41%nat)) + (V 42%nat)) <= 134217728 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat))) -> L5.u64_at RSEGS M ((V 2%nat) - 40) ((V 40%nat) + ((V 41%nat) + (V 43%nat))) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 37%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 37%nat) + 8) <= bv_unsigned a < ((V 37%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> ~ (((V 37%nat) + 8) <= i < ((V 37%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5fbc M) (st fx' R' 0xb5a7c M')
        /\ (forall x, In x KS_avaC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
        /\ getr R' (reg 14) = Z_to_bv 64 2147450880
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 37%nat) + 8) ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 744044
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 40%nat) + ((V 41%nat) + (V 43%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G1 G2 G8 G9 G10 G11 G12 K0 K1 K2 pvzI10 K4 K5 pvzI11 K7 K8 K9 K10 K11 pvzI12 pvzI13 pvzI14 K15 pvzI15 pvzI16 K18 K19 K20 K21 K22 K23 K24.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV41l; move HV41l before pvzI4; pose proof (proj2 pvzI4) as HV41r; move HV41r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV43l; move HV43l before pvzI6; pose proof (proj2 pvzI6) as HV43r; move HV43r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV49l; move HV49l before pvzI8; pose proof (proj2 pvzI8) as HV49r; move HV49r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K6l; move K6l before pvzI11; pose proof (proj2 pvzI11) as K6r; move K6r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K12l; move K12l before pvzI12; pose proof (proj2 pvzI12) as K12r; move K12r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K13l; move K13l before pvzI13; pose proof (proj2 pvzI13) as K13r; move K13r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K14l; move K14l before pvzI14; pose proof (proj2 pvzI14) as K14r; move K14r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K16l; move K16l before pvzI15; pose proof (proj2 pvzI15) as K16r; move K16r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K17l; move K17l before pvzI16; pose proof (proj2 pvzI16) as K17r; move K17r before pvzI16; clear pvzI16.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 40%nat => vz_40 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PavaC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavaC.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavaC.kn0).
  { unfold know_ok, PavaC.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K17l K17r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K13l K13r) | evalEk ZA ltac:(clear - HV42l HV42r K16l K16r K17l K17r) | clear - HV40l HV40r K13l K13r HV42l HV42r K16l K16r K17l K17r; lia | clear - HV40l HV40r K13l K13r HV42l HV42r K16l K16r K17l K17r; lia | clear - HV40l HV40r K13l K13r HV42l HV42r K16l K16r K17l K17r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K16l K16r K17l K17r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K17l K17r HV42l HV42r K16l K16r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r HV41l HV41r K14l K14r K17l K17r HV43l HV43r K12l K12r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r HV41l HV41r K14l K14r K17l K17r HV43l HV43r K12l K12r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K24]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavaC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavaC.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> ~ ((vz_37 + 8) <= bv_unsigned a < (vz_37 + 8) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PavaC.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavaC.ps0) with 0xb5a7c in Hms. change (SR.ps_regs PavaC.ps0) with (map (fun i => (i, nth i PavaC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavaC.ps0) with PavaC.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaC.regs0 PavaC.regs_out0 70 KS_avaC KS_avaC_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavaC.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavaC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaC.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PavaC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaC.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PavaC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaC.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PavaC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaC.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavaC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaC.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavaC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaC.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaC.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PavaC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaC.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PavaC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r HV41l HV41r K14l K14r K17l K17r HV43l HV43r K12l K12r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r HV41l HV41r K14l K14r K17l K17r HV43l HV43r K12l K12r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r HV41l HV41r K14l K14r K17l K17r HV43l HV43r K12l K12r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavaG := LibSegBa_avaG_b.
Definition KS_avaG : list nat := Eval vm_compute in (BG.kept_list 70 PavaG.regs0 PavaG.regs_out0).
Lemma KS_avaG_ok : BG.kept_ok 70 PavaG.regs0 PavaG.regs_out0 KS_avaG = true. Proof. vm_compute. reflexivity. Qed.
Lemma avaG_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 40) -> getr R (reg 9) = Z_to_bv 64 (V 46%nat) -> getr R (reg 10) = Z_to_bv 64 (V 44%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 19) = Z_to_bv 64 (V 41%nat) -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 40) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 128)) ->
  1 <= (V 43%nat) <= 134217728 -> 4096 <= (V 44%nat) <= 140737488355328 -> 0 <= (V 41%nat) <= 134217728 -> 1 <= (V 46%nat) <= 134217728 ->
  L5.writable RSEGS M (V 44%nat) (V 46%nat) -> (((V 2%nat) - 128) + 128 <= (V 44%nat) \/ (V 44%nat) + (V 46%nat) <= ((V 2%nat) - 128)) -> (2147446784 + 17592186048512 <= (V 44%nat) \/ (V 44%nat) + (V 46%nat) <= 2147446784) -> ((V 37%nat) + 24 <= (V 44%nat) \/ (V 44%nat) + (V 46%nat) <= (V 37%nat)) ->
  1 <= (((-1) * (V 41%nat)) + (V 46%nat)) <= 134217728 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 72) 743592 ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 52%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 112) (V 53%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) (V 54%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ (((V 44%nat) + 0) <= bv_unsigned a < ((V 44%nat) + 0) + (V 46%nat)) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> ~ (((V 44%nat) + 0) <= i < ((V 44%nat) + 0) + (V 46%nat)) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb5b00 M) (st fx' R' 0xb5c54 M')
        /\ (forall x, In x KS_avaG -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 743604
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 5) = Z_to_bv 64 ((((V 2%nat) - 32) / 8) + 2147450880)
        /\ getr R' (reg 6) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 7) = Z_to_bv 64 ((((V 41%nat) + (V 44%nat)) / 8) + 2147450880)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 41%nat) + (V 44%nat))
        /\ getr R' (reg 14) = Z_to_bv 64 ((((V 2%nat) - 48) / 8) + 2147450880)
        /\ getr R' (reg 15) = Z_to_bv 64 2147450880
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 41%nat) + (V 44%nat))
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 41%nat) + ((V 43%nat) + (V 44%nat)))
        /\ getr R' (reg 18) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 54%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 743604
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 44%nat) + (V 46%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 41%nat) + (V 44%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) ((V 41%nat) + (V 44%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 54%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G18 G19 G20 G21 K0 K1 K2 pvzI14 K4 K5 pvzI15 K7 K8 K9 K10 K11 pvzI16 pvzI17 pvzI18 pvzI19 K16 K17 K18 K19 pvzI20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV41l; move HV41l before pvzI3; pose proof (proj2 pvzI3) as HV41r; move HV41r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV46l; move HV46l before pvzI6; pose proof (proj2 pvzI6) as HV46r; move HV46r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV49l; move HV49l before pvzI8; pose proof (proj2 pvzI8) as HV49r; move HV49r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV52l; move HV52l before pvzI11; pose proof (proj2 pvzI11) as HV52r; move HV52r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV53l; move HV53l before pvzI12; pose proof (proj2 pvzI12) as HV53r; move HV53r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV54l; move HV54l before pvzI13; pose proof (proj2 pvzI13) as HV54r; move HV54r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K6l; move K6l before pvzI15; pose proof (proj2 pvzI15) as K6r; move K6r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K12l; move K12l before pvzI16; pose proof (proj2 pvzI16) as K12r; move K12r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K13l; move K13l before pvzI17; pose proof (proj2 pvzI17) as K13r; move K13r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K14l; move K14l before pvzI18; pose proof (proj2 pvzI18) as K14r; move K14r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K15l; move K15l before pvzI19; pose proof (proj2 pvzI19) as K15r; move K15r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K20l; move K20l before pvzI20; pose proof (proj2 pvzI20) as K20r; move K20r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 46%nat => Z_to_bv 64 vz_46 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 41%nat => vz_41 | 43%nat => vz_43 | 44%nat => vz_44 | 46%nat => vz_46 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PavaG.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavaG.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavaG.kn0).
  { unfold know_ok, PavaG.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11 K19) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11 K19) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11 K19) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11 K19) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11 K19; lia | clear - HV37l HV37r K6l K6r K8 K11 K19; lia | clear - HV37l HV37r K6l K6r K8 K11 K19; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11 K19) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11 K19; lia | clear - HV37l HV37r K6l K6r K8 K11 K19; lia | clear - HV37l HV37r K6l K6r K8 K11 K19; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11 K19) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K13l K13r K17 K18 K19) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K20l K20r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K15l K15r K20l K20r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV44l HV44r K13l K13r K17 K18 K19) | evalEk ZA ltac:(clear - HV46l HV46r K15l K15r K20l K20r) | clear - HV44l HV44r K13l K13r K17 K18 K19 HV46l HV46r K15l K15r K20l K20r; lia | clear - HV44l HV44r K13l K13r K17 K18 K19 HV46l HV46r K15l K15r K20l K20r; lia | clear - HV44l HV44r K13l K13r K17 K18 K19 HV46l HV46r K15l K15r K20l K20r; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV44l HV44r K13l K13r K17 K18 K19) | evalEk ZA ltac:(clear - HV46l HV46r K15l K15r K20l K20r) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV44l HV44r K13l K13r K17 K18 K19) | evalEk ZA ltac:(clear - HV46l HV46r K15l K15r K20l K20r) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11 K19) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV44l HV44r K13l K13r K17 K18 K19) | evalEk ZA ltac:(clear - HV46l HV46r K15l K15r K20l K20r) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K14l K14r K20l K20r HV46l HV46r K15l K15r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11 K19) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11 K19) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV43l HV43r K12l K12r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K3l K3r K11 K17; lia | clear - HV2l HV2r K3l K3r K11 K17; lia | exactA K33]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavaG.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavaG.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> ~ ((vz_44 + 0) <= bv_unsigned a < (vz_44 + 0) + vz_46) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PavaG.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 K17 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV44l HV44r K13l K13r K17 K18 K19) | evalEk' ZA Hag ltac:(clear - HV46l HV46r K15l K15r K20l K20r) | clear - HV44l HV44r K13l K13r K17 K18 K19 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavaG.ps0) with 0xb5c54 in Hms. change (SR.ps_regs PavaG.ps0) with (map (fun i => (i, nth i PavaG.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavaG.ps0) with PavaG.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaG.regs0 PavaG.regs_out0 70 KS_avaG KS_avaG_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 7 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaG.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PavaG.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV44l HV44r K13l K13r K17 K18 K19 HV46l HV46r K15l K15r K20l K20r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K14l K14r K20l K20r HV44l HV44r K13l K13r K17 K18 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K14l K14r K20l K20r HV44l HV44r K13l K13r K17 K18 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV44l HV44r K13l K13r K17 K18 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11 K19) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K12l K12r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV51l HV51r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV53l HV53r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11 K17) | evalEk' ZA Hag ltac:(clear - HV54l HV54r) | clear; lia].
Qed.
(* [comment removed for export] *)

Module PavaGL := LibSegBa_avaGL_b.
Definition KS_avaGL_0 : list nat := Eval vm_compute in (BG.kept_list 70 PavaGL.regs0 PavaGL.regs_out0).
Lemma KS_avaGL_0_ok : BG.kept_ok 70 PavaGL.regs0 PavaGL.regs_out0 KS_avaGL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avaGL_1 : list nat := Eval vm_compute in (BG.kept_list 70 PavaGL.regs0 PavaGL.regs_out1).
Lemma KS_avaGL_1_ok : BG.kept_ok 70 PavaGL.regs0 PavaGL.regs_out1 KS_avaGL_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avaGL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 743604 -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 5) = Z_to_bv 64 ((((V 2%nat) - 32) / 8) + 2147450880) -> getr R (reg 6) = Z_to_bv 64 18446744073709551615 -> getr R (reg 7) = Z_to_bv 64 ((((V 44%nat) + (V 56%nat)) / 8) + 2147450880) -> getr R (reg 8) = Z_to_bv 64 (V 37%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 11) = Z_to_bv 64 (((V 41%nat) + (V 43%nat)) - (V 56%nat)) -> getr R (reg 12) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 13) = Z_to_bv 64 ((V 44%nat) + (V 56%nat)) -> getr R (reg 14) = Z_to_bv 64 ((((V 2%nat) - 48) / 8) + 2147450880) -> getr R (reg 15) = Z_to_bv 64 2147450880 -> getr R (reg 16) = Z_to_bv 64 ((V 44%nat) + (V 56%nat)) -> getr R (reg 17) = Z_to_bv 64 ((V 41%nat) + ((V 43%nat) + (V 44%nat))) -> getr R (reg 18) = Z_to_bv 64 (V 51%nat) -> getr R (reg 19) = Z_to_bv 64 (V 52%nat) -> getr R (reg 20) = Z_to_bv 64 (V 53%nat) -> getr R (reg 21) = Z_to_bv 64 (V 54%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) 743604 -> L5.u64_at RSEGS M ((V 2%nat) - 40) ((V 44%nat) + (V 46%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 41%nat) + (V 44%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 48) ((V 41%nat) + (V 44%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 44%nat) -> L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 ->
  140735332487264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 37%nat) <= 140737488355304 ->
  aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 ->
  (((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 128)) -> 1 <= (V 43%nat) <= 134217728 -> 4096 <= (V 44%nat) <= 140737488355328 -> 0 <= (V 41%nat) <= 134217728 ->
  1 <= (V 46%nat) <= 134217728 -> L5.writable RSEGS M (V 44%nat) (V 46%nat) -> (((V 2%nat) - 128) + 128 <= (V 44%nat) \/ (V 44%nat) + (V 46%nat) <= ((V 2%nat) - 128)) -> (2147446784 + 17592186048512 <= (V 44%nat) \/ (V 44%nat) + (V 46%nat) <= 2147446784) ->
  ((V 37%nat) + 24 <= (V 44%nat) \/ (V 44%nat) + (V 46%nat) <= (V 37%nat)) -> 1 <= (((-1) * (V 41%nat)) + (V 46%nat)) <= 134217728 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) (V 54%nat) -> 0 <= (V 56%nat) <= 134217728 -> 0 <= (((-1) * (V 41%nat)) + (V 56%nat)) <= 134217728 -> 1 <= (((-1) * (V 56%nat)) + ((V 41%nat) + (V 43%nat))) <= 134217728 ->
  1 <= (((-1) * (V 56%nat)) + (V 46%nat)) <= 134217728 -> L5.u8_at RSEGS M ((((V 44%nat) + (V 56%nat)) / 8) + 2147450880) (V 55%nat) -> 0 <= (V 55%nat) <= 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ ((((V 44%nat) + (V 56%nat)) + 0) <= bv_unsigned a < (((V 44%nat) + (V 56%nat)) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> ~ ((((V 44%nat) + (V 56%nat)) + 0) <= i < (((V 44%nat) + (V 56%nat)) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c54 M) (st fx' R' 0xb5cb8 M')
        /\ (forall x, In x KS_avaGL_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 743616
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 7) = Z_to_bv 64 0
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 44%nat) + (V 56%nat)) + 1)
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 41%nat) + ((V 43%nat) + (V 44%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) ((V 41%nat) + ((V 43%nat) + (V 44%nat)))
        /\ (((((((V 41%nat) + (((V 43%nat) + ((18446744073709551615 * (V 56%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ L5.u8_at RSEGS M' ((V 44%nat) + (V 56%nat)) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 743604
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 44%nat) + (V 46%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 41%nat) + (V 44%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 54%nat))
      \/ (msteps RSEGS (st fx R 0xb5c54 M) (st fx' R' 0xb5c54 M')
        /\ (forall x, In x KS_avaGL_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 7) = Z_to_bv 64 (((((V 44%nat) + (V 56%nat)) + 1) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 41%nat) + ((V 43%nat) - (V 56%nat))) - 1)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 44%nat) + (V 56%nat)) + 1)
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 44%nat) + (V 56%nat)) + 1)
        /\ 1 <= (((((((V 41%nat) + (((V 43%nat) + ((18446744073709551615 * (V 56%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64) - 0) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' ((V 44%nat) + (V 56%nat)) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 743604
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 44%nat) + (V 46%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 41%nat) + (V 44%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) ((V 41%nat) + (V 44%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 54%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G1 G2 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 K0 K1 K2 K3 K4 K5 K6 K7 pvzI16 K9 K10 pvzI17 K12 K13 K14 K15 K16 pvzI18 pvzI19 pvzI20 pvzI21 K21 K22 K23 K24 pvzI22 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 pvzI23 pvzI24 pvzI25 pvzI26 K41 pvzI27.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV41l; move HV41l before pvzI3; pose proof (proj2 pvzI3) as HV41r; move HV41r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV46l; move HV46l before pvzI6; pose proof (proj2 pvzI6) as HV46r; move HV46r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV49l; move HV49l before pvzI8; pose proof (proj2 pvzI8) as HV49r; move HV49r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV52l; move HV52l before pvzI11; pose proof (proj2 pvzI11) as HV52r; move HV52r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV53l; move HV53l before pvzI12; pose proof (proj2 pvzI12) as HV53r; move HV53r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV54l; move HV54l before pvzI13; pose proof (proj2 pvzI13) as HV54r; move HV54r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV55l; move HV55l before pvzI14; pose proof (proj2 pvzI14) as HV55r; move HV55r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV56l; move HV56l before pvzI15; pose proof (proj2 pvzI15) as HV56r; move HV56r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K8l; move K8l before pvzI16; pose proof (proj2 pvzI16) as K8r; move K8r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K11l; move K11l before pvzI17; pose proof (proj2 pvzI17) as K11r; move K11r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K17l; move K17l before pvzI18; pose proof (proj2 pvzI18) as K17r; move K17r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K18l; move K18l before pvzI19; pose proof (proj2 pvzI19) as K18r; move K18r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K19l; move K19l before pvzI20; pose proof (proj2 pvzI20) as K19r; move K19r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K20l; move K20l before pvzI21; pose proof (proj2 pvzI21) as K20r; move K20r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K25l; move K25l before pvzI22; pose proof (proj2 pvzI22) as K25r; move K25r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K37l; move K37l before pvzI23; pose proof (proj2 pvzI23) as K37r; move K37r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K38l; move K38l before pvzI24; pose proof (proj2 pvzI24) as K38r; move K38r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K39l; move K39l before pvzI25; pose proof (proj2 pvzI25) as K39r; move K39r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K40l; move K40l before pvzI26; pose proof (proj2 pvzI26) as K40r; move K40r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K42l; move K42l before pvzI27; pose proof (proj2 pvzI27) as K42r; move K42r before pvzI27; clear pvzI27.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 46%nat => Z_to_bv 64 vz_46 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 41%nat => vz_41 | 43%nat => vz_43 | 44%nat => vz_44 | 46%nat => vz_46 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PavaGL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavaGL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavaGL.kn0).
  { unfold know_ok, PavaGL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K22 K23 K24 HV46l HV46r K20l K20r K25l K25r K40l K40r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV44l HV44r K18l K18r K22 K23 K24) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV44l HV44r K18l K18r K22 K23 K24) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K22 K23 K24) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K11l K11r K13 K16 K24; lia | clear - HV37l HV37r K11l K11r K13 K16 K24; lia | clear - HV37l HV37r K11l K11r K13 K16 K24; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K11l K11r K13 K16 K24; lia | clear - HV37l HV37r K11l K11r K13 K16 K24; lia | clear - HV37l HV37r K11l K11r K13 K16 K24; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K17l K17r K39l K39r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K22 K23 K24) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K20l K20r K25l K25r K40l K40r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K22 K23 K24) | evalEk ZA ltac:(clear - HV46l HV46r K20l K20r K25l K25r K40l K40r) | clear - HV44l HV44r K18l K18r K22 K23 K24 HV46l HV46r K20l K20r K25l K25r K40l K40r; lia | clear - HV44l HV44r K18l K18r K22 K23 K24 HV46l HV46r K20l K20r K25l K25r K40l K40r; lia | clear - HV44l HV44r K18l K18r K22 K23 K24 HV46l HV46r K20l K20r K25l K25r K40l K40r; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K22 K23 K24) | evalEk ZA ltac:(clear - HV46l HV46r K20l K20r K25l K25r K40l K40r) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K22 K23 K24) | evalEk ZA ltac:(clear - HV46l HV46r K20l K20r K25l K25r K40l K40r) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K22 K23 K24) | evalEk ZA ltac:(clear - HV46l HV46r K20l K20r K25l K25r K40l K40r) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV46l HV46r K20l K20r K40l K40r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV43l HV43r K17l K17r K39l K39r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV56l HV56r K37l K37r K40l K40r) | exact (conj K38l K38r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV43l HV43r K17l K17r HV56l HV56r K37l K37r K40l K40r) | exact (conj K39l K39r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K20l K20r K25l K25r K40l K40r HV56l HV56r K37l K37r K38l K38r K39l K39r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K22 K23 K24 HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r) | evalEk ZA ltac:(clear - HV55l HV55r K42l K42r) | clear - HV44l HV44r K18l K18r K22 K23 K24 HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r; lia | clear - HV44l HV44r K18l K18r K22 K23 K24 HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r; lia | byte_tac ltac:(clear - HV55l HV55r K42l K42r) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K42l K42r) | exact (conj K42l K42r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavaGL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavaGL.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> ~ (((vz_44 + vz_56) + 0) <= bv_unsigned a < ((vz_44 + vz_56) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PavaGL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K8l K8r K16 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV44l HV44r K18l K18r K22 K23 K24 HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r) | evalEk' ZA Hag ltac:(clear) | clear - HV44l HV44r K18l K18r K22 K23 K24 HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PavaGL.ps0) with 0xb5cb8 in Hms. change (SR.ps_regs PavaGL.ps0) with (map (fun i => (i, nth i PavaGL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavaGL.ps0) with PavaGL.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaGL.regs0 PavaGL.regs_out0 70 KS_avaGL_0 KS_avaGL_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavaGL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavaGL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PavaGL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL.regs_out0 E' R' 7 Hregs) by (clear; lia). cbn [nth PavaGL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavaGL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavaGL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaGL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PavaGL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV43l HV43r K17l K17r HV44l HV44r K18l K18r K22 K23 K24) | clear; lia]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV44l HV44r K18l K18r K22 K23 K24 HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV44l HV44r K18l K18r K22 K23 K24 HV46l HV46r K20l K20r K25l K25r K40l K40r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV44l HV44r K18l K18r K22 K23 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV44l HV44r K18l K18r K22 K23 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K17l K17r K39l K39r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV51l HV51r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV53l HV53r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV54l HV54r) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right.
    change (SR.ps_pc PavaGL.ps1) with 0xb5c54 in Hms. change (SR.ps_regs PavaGL.ps1) with (map (fun i => (i, nth i PavaGL.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavaGL.ps1) with PavaGL.cells1 in Hcells. unfold PavaGL.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaGL.regs0 PavaGL.regs_out1 70 KS_avaGL_1 KS_avaGL_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavaGL.regs_out1 E' R' 7 Hregs) by (clear; lia). cbn [nth PavaGL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavaGL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaGL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL.regs_out1 E' R' 16 Hregs) by (clear; lia). cbn [nth PavaGL.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV44l HV44r K18l K18r K22 K23 K24 HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV44l HV44r K18l K18r K22 K23 K24 HV46l HV46r K20l K20r K25l K25r K40l K40r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV44l HV44r K18l K18r K22 K23 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV44l HV44r K18l K18r K22 K23 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV44l HV44r K18l K18r K22 K23 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K17l K17r K39l K39r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV51l HV51r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV53l HV53r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV54l HV54r) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

Module PavaGL1 := LibSegBa_avaGL1_b.
Definition KS_avaGL1_0 : list nat := Eval vm_compute in (BG.kept_list 70 PavaGL1.regs0 PavaGL1.regs_out0).
Lemma KS_avaGL1_0_ok : BG.kept_ok 70 PavaGL1.regs0 PavaGL1.regs_out0 KS_avaGL1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avaGL1_1 : list nat := Eval vm_compute in (BG.kept_list 70 PavaGL1.regs0 PavaGL1.regs_out1).
Lemma KS_avaGL1_1_ok : BG.kept_ok 70 PavaGL1.regs0 PavaGL1.regs_out1 KS_avaGL1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avaGL1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 743604 -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 5) = Z_to_bv 64 ((((V 2%nat) - 32) / 8) + 2147450880) -> getr R (reg 6) = Z_to_bv 64 18446744073709551615 -> getr R (reg 7) = Z_to_bv 64 ((((V 44%nat) + (V 56%nat)) / 8) + 2147450880) -> getr R (reg 8) = Z_to_bv 64 (V 37%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 2%nat) - 48) -> getr R (reg 11) = Z_to_bv 64 (((V 41%nat) + (V 43%nat)) - (V 56%nat)) -> getr R (reg 12) = Z_to_bv 64 ((V 2%nat) - 32) -> getr R (reg 13) = Z_to_bv 64 ((V 44%nat) + (V 56%nat)) -> getr R (reg 14) = Z_to_bv 64 ((((V 2%nat) - 48) / 8) + 2147450880) -> getr R (reg 15) = Z_to_bv 64 2147450880 -> getr R (reg 16) = Z_to_bv 64 ((V 44%nat) + (V 56%nat)) -> getr R (reg 17) = Z_to_bv 64 ((V 41%nat) + ((V 43%nat) + (V 44%nat))) -> getr R (reg 18) = Z_to_bv 64 (V 51%nat) -> getr R (reg 19) = Z_to_bv 64 (V 52%nat) -> getr R (reg 20) = Z_to_bv 64 (V 53%nat) -> getr R (reg 21) = Z_to_bv 64 (V 54%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) 743604 -> L5.u64_at RSEGS M ((V 2%nat) - 40) ((V 44%nat) + (V 46%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 41%nat) + (V 44%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 48) ((V 41%nat) + (V 44%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 44%nat) -> L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 ->
  140735332487264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 37%nat) <= 140737488355304 ->
  aligned (V 37%nat) 8 -> (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 ->
  (((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 128)) -> 1 <= (V 43%nat) <= 134217728 -> 4096 <= (V 44%nat) <= 140737488355328 -> 0 <= (V 41%nat) <= 134217728 ->
  1 <= (V 46%nat) <= 134217728 -> L5.writable RSEGS M (V 44%nat) (V 46%nat) -> (((V 2%nat) - 128) + 128 <= (V 44%nat) \/ (V 44%nat) + (V 46%nat) <= ((V 2%nat) - 128)) -> (2147446784 + 17592186048512 <= (V 44%nat) \/ (V 44%nat) + (V 46%nat) <= 2147446784) ->
  ((V 37%nat) + 24 <= (V 44%nat) \/ (V 44%nat) + (V 46%nat) <= (V 37%nat)) -> 1 <= (((-1) * (V 41%nat)) + (V 46%nat)) <= 134217728 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 37%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 112) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) (V 54%nat) -> 0 <= (V 56%nat) <= 134217728 -> 0 <= (((-1) * (V 41%nat)) + (V 56%nat)) <= 134217728 -> 1 <= (((-1) * (V 56%nat)) + ((V 41%nat) + (V 43%nat))) <= 134217728 ->
  1 <= (((-1) * (V 56%nat)) + (V 46%nat)) <= 134217728 -> L5.u8_at RSEGS M ((((V 44%nat) + (V 56%nat)) / 8) + 2147450880) (V 55%nat) -> 1 <= (V 55%nat) <= 7 -> 1 <= ((V 55%nat) - (Z.land ((V 44%nat) + (V 56%nat)) 7)) <= 7 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> ~ ((((V 44%nat) + (V 56%nat)) + 0) <= bv_unsigned a < (((V 44%nat) + (V 56%nat)) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> ~ ((((V 44%nat) + (V 56%nat)) + 0) <= i < (((V 44%nat) + (V 56%nat)) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb5c54 M) (st fx' R' 0xb5cb8 M')
        /\ (forall x, In x KS_avaGL1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 743616
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 7) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 44%nat) + (V 56%nat)) + 1)
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 41%nat) + ((V 43%nat) + (V 44%nat)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) ((V 41%nat) + ((V 43%nat) + (V 44%nat)))
        /\ (((((((V 41%nat) + (((V 43%nat) + ((18446744073709551615 * (V 56%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64) - 0) mod 2 ^ 64) < 1
        /\ L5.u8_at RSEGS M' ((V 44%nat) + (V 56%nat)) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 743604
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 44%nat) + (V 46%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 41%nat) + (V 44%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 54%nat))
      \/ (msteps RSEGS (st fx R 0xb5c54 M) (st fx' R' 0xb5c54 M')
        /\ (forall x, In x KS_avaGL1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 7) = Z_to_bv 64 (((((V 44%nat) + (V 56%nat)) + 1) / 8) + 2147450880)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 41%nat) + ((V 43%nat) - (V 56%nat))) - 1)
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 44%nat) + (V 56%nat)) + 1)
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 44%nat) + (V 56%nat)) + 1)
        /\ 1 <= (((((((V 41%nat) + (((V 43%nat) + ((18446744073709551615 * (V 56%nat)) mod 2 ^ 64)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64) - 0) mod 2 ^ 64)
        /\ L5.u8_at RSEGS M' ((V 44%nat) + (V 56%nat)) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 743604
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 44%nat) + (V 46%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 41%nat) + (V 44%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) ((V 41%nat) + (V 44%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 112) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 54%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 G1 G2 G5 G6 G7 G8 G9 G10 G11 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 K0 K1 K2 K3 K4 K5 K6 K7 pvzI16 K9 K10 pvzI17 K12 K13 K14 K15 K16 pvzI18 pvzI19 pvzI20 pvzI21 K21 K22 K23 K24 pvzI22 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 pvzI23 pvzI24 pvzI25 pvzI26 K41 pvzI27 pvzI28.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV41l; move HV41l before pvzI3; pose proof (proj2 pvzI3) as HV41r; move HV41r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV43l; move HV43l before pvzI4; pose proof (proj2 pvzI4) as HV43r; move HV43r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV44l; move HV44l before pvzI5; pose proof (proj2 pvzI5) as HV44r; move HV44r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV46l; move HV46l before pvzI6; pose proof (proj2 pvzI6) as HV46r; move HV46r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV49l; move HV49l before pvzI8; pose proof (proj2 pvzI8) as HV49r; move HV49r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV51l; move HV51l before pvzI10; pose proof (proj2 pvzI10) as HV51r; move HV51r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV52l; move HV52l before pvzI11; pose proof (proj2 pvzI11) as HV52r; move HV52r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV53l; move HV53l before pvzI12; pose proof (proj2 pvzI12) as HV53r; move HV53r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV54l; move HV54l before pvzI13; pose proof (proj2 pvzI13) as HV54r; move HV54r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV55l; move HV55l before pvzI14; pose proof (proj2 pvzI14) as HV55r; move HV55r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV56l; move HV56l before pvzI15; pose proof (proj2 pvzI15) as HV56r; move HV56r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K8l; move K8l before pvzI16; pose proof (proj2 pvzI16) as K8r; move K8r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K11l; move K11l before pvzI17; pose proof (proj2 pvzI17) as K11r; move K11r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K17l; move K17l before pvzI18; pose proof (proj2 pvzI18) as K17r; move K17r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K18l; move K18l before pvzI19; pose proof (proj2 pvzI19) as K18r; move K18r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K19l; move K19l before pvzI20; pose proof (proj2 pvzI20) as K19r; move K19r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K20l; move K20l before pvzI21; pose proof (proj2 pvzI21) as K20r; move K20r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K25l; move K25l before pvzI22; pose proof (proj2 pvzI22) as K25r; move K25r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K37l; move K37l before pvzI23; pose proof (proj2 pvzI23) as K37r; move K37r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K38l; move K38l before pvzI24; pose proof (proj2 pvzI24) as K38r; move K38r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K39l; move K39l before pvzI25; pose proof (proj2 pvzI25) as K39r; move K39r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K40l; move K40l before pvzI26; pose proof (proj2 pvzI26) as K40r; move K40r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K42l; move K42l before pvzI27; pose proof (proj2 pvzI27) as K42r; move K42r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K43l; move K43l before pvzI28; pose proof (proj2 pvzI28) as K43r; move K43r before pvzI28; clear pvzI28.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_44 := V 44%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 44%nat => Z_to_bv 64 vz_44 | 46%nat => Z_to_bv 64 vz_46 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 41%nat => vz_41 | 43%nat => vz_43 | 44%nat => vz_44 | 46%nat => vz_46 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | 55%nat => vz_55 | 56%nat => vz_56 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 57%nat. }
  assert (HR: regs_ok E PavaGL1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavaGL1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavaGL1.kn0).
  { unfold know_ok, PavaGL1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24 HV46l HV46r K20l K20r K25l K25r K40l K40r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV44l HV44r K18l K18r K43l K43r K22 K23 K24) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV44l HV44r K18l K18r K43l K43r K22 K23 K24) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K11l K11r K13 K16 K24; lia | clear - HV37l HV37r K11l K11r K13 K16 K24; lia | clear - HV37l HV37r K11l K11r K13 K16 K24; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K11l K11r K13 K16 K24; lia | clear - HV37l HV37r K11l K11r K13 K16 K24; lia | clear - HV37l HV37r K11l K11r K13 K16 K24; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K17l K17r K39l K39r) | exact (conj K17l K17r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24) | exact (conj K18l K18r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K20l K20r K25l K25r K40l K40r) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24) | evalEk ZA ltac:(clear - HV46l HV46r K20l K20r K25l K25r K40l K40r) | clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24 HV46l HV46r K20l K20r K25l K25r K40l K40r; lia | clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24 HV46l HV46r K20l K20r K25l K25r K40l K40r; lia | clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24 HV46l HV46r K20l K20r K25l K25r K40l K40r; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24) | evalEk ZA ltac:(clear - HV46l HV46r K20l K20r K25l K25r K40l K40r) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24) | evalEk ZA ltac:(clear - HV46l HV46r K20l K20r K25l K25r K40l K40r) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24) | evalEk ZA ltac:(clear - HV46l HV46r K20l K20r K25l K25r K40l K40r) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV46l HV46r K20l K20r K40l K40r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV43l HV43r K17l K17r K39l K39r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K8l K8r K16 K22; lia | clear - HV2l HV2r K8l K8r K16 K22; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r K43l K43r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV56l HV56r K37l K37r K40l K40r K43l K43r) | exact (conj K38l K38r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV43l HV43r K17l K17r HV56l HV56r K37l K37r K40l K40r K43l K43r) | exact (conj K39l K39r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K20l K20r K25l K25r K40l K40r HV56l HV56r K37l K37r K38l K38r K39l K39r K43l K43r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24 HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r) | evalEk ZA ltac:(clear - HV55l HV55r K42l K42r K43l K43r) | clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24 HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r; lia | clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24 HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r; lia | byte_tac ltac:(clear - HV55l HV55r K42l K42r K43l K43r) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV55l HV55r K42l K42r K43l K43r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [(L5K.evalB ZA; pvz_unfold ZA); reflexivity | repeat match goal with |- context [Z.land (?x mod 2 ^ 64) ?k] => rewrite (Z.mod_small x (2 ^ 64)) by lia end; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavaGL1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavaGL1.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> ~ (((vz_44 + vz_56) + 0) <= bv_unsigned a < ((vz_44 + vz_56) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PavaGL1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K8l K8r K16 K22 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24 HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r) | evalEk' ZA Hag ltac:(clear) | clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24 HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PavaGL1.ps0) with 0xb5cb8 in Hms. change (SR.ps_regs PavaGL1.ps0) with (map (fun i => (i, nth i PavaGL1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavaGL1.ps0) with PavaGL1.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaGL1.regs0 PavaGL1.regs_out0 70 KS_avaGL1_0 KS_avaGL1_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavaGL1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavaGL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PavaGL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL1.regs_out0 E' R' 7 Hregs) by (clear; lia). cbn [nth PavaGL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavaGL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavaGL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaGL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL1.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PavaGL1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV43l HV43r K17l K17r HV44l HV44r K18l K18r K43l K43r K22 K23 K24) | clear; lia]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24 HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24 HV46l HV46r K20l K20r K25l K25r K40l K40r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV44l HV44r K18l K18r K43l K43r K22 K23 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K17l K17r K39l K39r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV51l HV51r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV53l HV53r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV54l HV54r) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right.
    change (SR.ps_pc PavaGL1.ps1) with 0xb5c54 in Hms. change (SR.ps_regs PavaGL1.ps1) with (map (fun i => (i, nth i PavaGL1.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavaGL1.ps1) with PavaGL1.cells1 in Hcells. unfold PavaGL1.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaGL1.regs0 PavaGL1.regs_out1 70 KS_avaGL1_1 KS_avaGL1_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavaGL1.regs_out1 E' R' 7 Hregs) by (clear; lia). cbn [nth PavaGL1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL1.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavaGL1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL1.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaGL1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaGL1.regs_out1 E' R' 16 Hregs) by (clear; lia). cbn [nth PavaGL1.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24 HV56l HV56r K37l K37r K38l K38r K39l K39r K40l K40r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24 HV46l HV46r K20l K20r K25l K25r K40l K40r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV44l HV44r K18l K18r K43l K43r K22 K23 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV41l HV41r K19l K19r K25l K25r K38l K38r K39l K39r HV44l HV44r K18l K18r K43l K43r K22 K23 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV44l HV44r K18l K18r K43l K43r K22 K23 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K11l K11r K13 K16 K24) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K17l K17r K39l K39r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV51l HV51r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV52l HV52r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV53l HV53r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K8l K8r K16 K22) | evalEk' ZA Hag ltac:(clear - HV54l HV54r) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.

(* [comment removed for export] *)
Module PavaI := LibSegBa_avaI_b.
Definition KS_avaI_0 : list nat := Eval vm_compute in (BG.kept_list 70 PavaI.regs0 PavaI.regs_out0).
Lemma KS_avaI_0_ok : BG.kept_ok 70 PavaI.regs0 PavaI.regs_out0 KS_avaI_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_avaI_1 : list nat := Eval vm_compute in (BG.kept_list 70 PavaI.regs0 PavaI.regs_out1).
Lemma KS_avaI_1_ok : BG.kept_ok 70 PavaI.regs0 PavaI.regs_out1 KS_avaI_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma avaI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 37%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 18) = Z_to_bv 64 (V 51%nat) -> getr R (reg 19) = Z_to_bv 64 (V 52%nat) -> getr R (reg 20) = Z_to_bv 64 (V 53%nat) -> getr R (reg 21) = Z_to_bv 64 (V 54%nat) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 128) + 128 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 128)) ->
  1 <= (V 43%nat) <= 134217728 -> 0 <= (V 40%nat) <= 140737488355328 -> 0 <= (V 42%nat) <= 134217728 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) ((V 40%nat) + (V 42%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 40%nat) -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb58c0 M) (st fx' R' 0xd39ac M')
        /\ (forall x, In x KS_avaI_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 743624
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 ((((V 2%nat) - 48) / 8) + 2147450880)
        /\ getr R' (reg 16) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 17) = Z_to_bv 64 (V 40%nat)
        /\ 1 <= (((V 40%nat) - 0) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 743624
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 40%nat) + (V 42%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 40%nat))
      \/ (msteps RSEGS (st fx R 0xb58c0 M) (st fx' R' 0xb58d8 M')
        /\ (forall x, In x KS_avaI_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 32)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 2%nat) - 32) / 8)
        /\ getr R' (reg 15) = Z_to_bv 64 ((((V 2%nat) - 48) / 8) + 2147450880)
        /\ getr R' (reg 16) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 17) = Z_to_bv 64 (V 40%nat)
        /\ (((V 40%nat) - 0) mod 2 ^ 64) < 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 743624
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) ((V 40%nat) + (V 42%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 40%nat))).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G18 G19 G20 G21 K0 K1 K2 pvzI13 K4 K5 pvzI14 K7 K8 K9 K10 K11 pvzI15 pvzI16 pvzI17 K15 K16 K17 K18 K19 K20 K21 K22 K23.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV42l; move HV42l before pvzI4; pose proof (proj2 pvzI4) as HV42r; move HV42r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV49l; move HV49l before pvzI7; pose proof (proj2 pvzI7) as HV49r; move HV49r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV51l; move HV51l before pvzI9; pose proof (proj2 pvzI9) as HV51r; move HV51r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV52l; move HV52l before pvzI10; pose proof (proj2 pvzI10) as HV52r; move HV52r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV53l; move HV53l before pvzI11; pose proof (proj2 pvzI11) as HV53r; move HV53r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV54l; move HV54l before pvzI12; pose proof (proj2 pvzI12) as HV54r; move HV54r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K3l; move K3l before pvzI13; pose proof (proj2 pvzI13) as K3r; move K3r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K6l; move K6l before pvzI14; pose proof (proj2 pvzI14) as K6r; move K6r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K13l; move K13l before pvzI16; pose proof (proj2 pvzI16) as K13r; move K13r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K14l; move K14l before pvzI17; pose proof (proj2 pvzI17) as K14r; move K14r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 40%nat => vz_40 | 42%nat => vz_42 | 43%nat => vz_43 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PavaI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavaI.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavaI.kn0).
  { unfold know_ok, PavaI.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r HV42l HV42r K14l K14r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K22]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K23]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavaI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavaI.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PavaI.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. left.
    change (SR.ps_pc PavaI.ps0) with 0xd39ac in Hms. change (SR.ps_regs PavaI.ps0) with (map (fun i => (i, nth i PavaI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavaI.ps0) with PavaI.cells0 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaI.regs0 PavaI.regs_out0 70 KS_avaI_0 KS_avaI_0_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavaI.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavaI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PavaI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PavaI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PavaI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PavaI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PavaI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PavaI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PavaI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r HV42l HV42r K14l K14r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r) | clear; lia].
  }
  destruct kk as [|kk].
  { cbn in Hnth. injection Hnth as Hps. subst ps. right.
    change (SR.ps_pc PavaI.ps1) with 0xb58d8 in Hms. change (SR.ps_regs PavaI.ps1) with (map (fun i => (i, nth i PavaI.regs_out1 (ELit 0))) (seq 1 31)) in Hregs.
    change (SR.ps_cells PavaI.ps1) with PavaI.cells1 in Hcells. unfold PavaI.cells1 in Hcells.
    split. { exact Hms. }
    split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaI.regs0 PavaI.regs_out1 70 KS_avaI_1 KS_avaI_1_ok HR Hag Hregs j Hj). }
    split. { rewrite (BG.out_reg PavaI.regs_out1 E' R' 1 Hregs) by (clear; lia). cbn [nth PavaI.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out1 E' R' 2 Hregs) by (clear; lia). cbn [nth PavaI.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out1 E' R' 8 Hregs) by (clear; lia). cbn [nth PavaI.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out1 E' R' 9 Hregs) by (clear; lia). cbn [nth PavaI.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out1 E' R' 10 Hregs) by (clear; lia). cbn [nth PavaI.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out1 E' R' 11 Hregs) by (clear; lia). cbn [nth PavaI.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out1 E' R' 12 Hregs) by (clear; lia). cbn [nth PavaI.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out1 E' R' 13 Hregs) by (clear; lia). cbn [nth PavaI.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out1 E' R' 14 Hregs) by (clear; lia). cbn [nth PavaI.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out1 E' R' 15 Hregs) by (clear; lia). cbn [nth PavaI.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out1 E' R' 16 Hregs) by (clear; lia). cbn [nth PavaI.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { rewrite (BG.out_reg PavaI.regs_out1 E' R' 17 Hregs) by (clear; lia). cbn [nth PavaI.regs_out1]. first [reflexivity | wordP' ZA Hag]. }
    split. { (let HR := fresh "HR" in eassert (HR : _ <= _ <= _) by (eapply L5K.range_of_KRange; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | ((L5K.evalB' ZA Hag; pvz_unfold ZA); den_tac)]); match type of HR with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec0 a b); lia end). }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV48l HV48r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV49l HV49r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV50l HV50r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r HV42l HV42r K14l K14r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r) | clear; lia]. }
    split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r) | clear; lia]. }
    eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K13l K13r) | clear; lia].
  }
  destruct kk; cbn in Hnth; discriminate.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PavaJ := LibSegBa_avaJ_b.
Definition KS_avaJ : list nat := Eval vm_compute in (BG.kept_list 70 PavaJ.regs0 PavaJ.regs_out0).
Lemma KS_avaJ_ok : BG.kept_ok 70 PavaJ.regs0 PavaJ.regs_out0 KS_avaJ = true. Proof. vm_compute. reflexivity. Qed.
Lemma avaJ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 37%nat) -> getr R (reg 9) = Z_to_bv 64 (V 43%nat) -> getr R (reg 18) = Z_to_bv 64 (V 51%nat) -> getr R (reg 19) = Z_to_bv 64 (V 52%nat) -> getr R (reg 20) = Z_to_bv 64 (V 53%nat) -> getr R (reg 21) = Z_to_bv 64 (V 54%nat) ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 140735332487264 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> 6905856 <= (V 37%nat) <= 140737488355304 -> aligned (V 37%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 37%nat) \/ (V 37%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 37%nat) / 8) + 2147450880) 3 -> L5.writable RSEGS M (V 37%nat) 24 -> (((V 2%nat) - 64) + 64 <= (V 37%nat) \/ (V 37%nat) + 24 <= ((V 2%nat) - 64)) ->
  1 <= (V 43%nat) <= 134217728 -> 0 <= (V 40%nat) <= 140737488355328 -> 0 <= (V 42%nat) <= 134217728 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 48%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 37%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) ((V 40%nat) + (V 42%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 40%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb58c8 M) (st fx' R' 0xb58d8 M')
        /\ (forall x, In x KS_avaJ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 50%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G18 G19 G20 G21 K0 K1 K2 pvzI13 K4 K5 pvzI14 K7 K8 K9 K10 K11 pvzI15 pvzI16 pvzI17 K15 K16 K17 K18 K19 K20 K21 K22.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV37l; move HV37l before pvzI2; pose proof (proj2 pvzI2) as HV37r; move HV37r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV40l; move HV40l before pvzI3; pose proof (proj2 pvzI3) as HV40r; move HV40r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV42l; move HV42l before pvzI4; pose proof (proj2 pvzI4) as HV42r; move HV42r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV43l; move HV43l before pvzI5; pose proof (proj2 pvzI5) as HV43r; move HV43r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV49l; move HV49l before pvzI7; pose proof (proj2 pvzI7) as HV49r; move HV49r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV50l; move HV50l before pvzI8; pose proof (proj2 pvzI8) as HV50r; move HV50r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV51l; move HV51l before pvzI9; pose proof (proj2 pvzI9) as HV51r; move HV51r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV52l; move HV52l before pvzI10; pose proof (proj2 pvzI10) as HV52r; move HV52r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV53l; move HV53l before pvzI11; pose proof (proj2 pvzI11) as HV53r; move HV53r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV54l; move HV54l before pvzI12; pose proof (proj2 pvzI12) as HV54r; move HV54r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K3l; move K3l before pvzI13; pose proof (proj2 pvzI13) as K3r; move K3r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K6l; move K6l before pvzI14; pose proof (proj2 pvzI14) as K6r; move K6r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K12l; move K12l before pvzI15; pose proof (proj2 pvzI15) as K12r; move K12r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K13l; move K13l before pvzI16; pose proof (proj2 pvzI16) as K13r; move K13r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K14l; move K14l before pvzI17; pose proof (proj2 pvzI17) as K14r; move K14r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_40 := V 40%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_49 := V 49%nat) in *. set (vz_50 := V 50%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_53 := V 53%nat) in *. set (vz_54 := V 54%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 37%nat => Z_to_bv 64 vz_37 | 40%nat => Z_to_bv 64 vz_40 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 48%nat => Z_to_bv 64 vz_48 | 49%nat => Z_to_bv 64 vz_49 | 50%nat => Z_to_bv 64 vz_50 | 51%nat => Z_to_bv 64 vz_51 | 52%nat => Z_to_bv 64 vz_52 | 53%nat => Z_to_bv 64 vz_53 | 54%nat => Z_to_bv 64 vz_54 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 37%nat => vz_37 | 40%nat => vz_40 | 42%nat => vz_42 | 43%nat => vz_43 | 48%nat => vz_48 | 49%nat => vz_49 | 50%nat => vz_50 | 51%nat => vz_51 | 52%nat => vz_52 | 53%nat => vz_53 | 54%nat => vz_54 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PavaJ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PavaJ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PavaJ.kn0).
  { unfold know_ok, PavaJ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | clear - HV37l HV37r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV37l HV37r K6l K6r K8 K11) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r HV42l HV42r K14l K14r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r K11) | evalEk ZA ltac:(clear - HV40l HV40r K13l K13r) | clear - HV2l HV2r K3l K3r K11; lia | clear - HV2l HV2r K3l K3r K11; lia | exactA K22]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PavaJ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PavaJ.NX0 with 70%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PavaJ.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PavaJ.ps0) with 0xb58d8 in Hms. change (SR.ps_regs PavaJ.ps0) with (map (fun i => (i, nth i PavaJ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PavaJ.ps0) with PavaJ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PavaJ.regs0 PavaJ.regs_out0 70 KS_avaJ KS_avaJ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PavaJ.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PavaJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaJ.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PavaJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PavaJ.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PavaJ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PavaJ.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PavaJ.regs_out0]. first [reflexivity | wordP' ZA Hag].
Qed.
(* [comment removed for export] *)

End PMAVGP.
