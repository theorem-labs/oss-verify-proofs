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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_adkD1_b LibSegBa_adkD2_b LibSegBa_adkZ1_b LibSegBa_adkSC_b LibSegBa_adkZ0_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNADP2.
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
Module PadkD1 := LibSegBa_adkD1_b.
Definition KS_adkD1_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkD1.regs0 PadkD1.regs_out0).
Lemma KS_adkD1_0_ok : BG.kept_ok 80 PadkD1.regs0 PadkD1.regs_out0 KS_adkD1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkD1_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkD1.regs0 PadkD1.regs_out1).
Lemma KS_adkD1_1_ok : BG.kept_ok 80 PadkD1.regs0 PadkD1.regs_out1 KS_adkD1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkD1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 ((V 34%nat) + 8) -> getr R (reg 11) = Z_to_bv 64 ((((V 34%nat) + 8) / 8) + 2147450880) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 34%nat) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 30) = Z_to_bv 64 (V 38%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 6905856 <= (V 34%nat) <= 140737488355312 ->
  aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 16 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 2 -> L5.u64_at RSEGS M (V 34%nat) (V 35%nat) ->
  L5.u64_at RSEGS M ((V 34%nat) + 8) (V 36%nat) -> (((V 2%nat) - 256) + 256 <= (V 34%nat) \/ (V 34%nat) + 16 <= ((V 2%nat) - 256)) -> 4096 <= (V 33%nat) <= 140737488355280 -> 0 <= ((V 38%nat) - (V 33%nat)) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb406c M) (st fx' R' 0xb40a4 M')
        /\ (forall x, In x KS_adkD1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ bv_unsigned (getr R' (reg 12)) = (((32768 * (V 36%nat)) mod 2 ^ 64) / 2305843009213693952)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) / 4294967296)
        /\ bv_unsigned (getr R' (reg 14)) = (Z.land ((V 36%nat) / 4294967296) 1610612736)
        /\ 1 <= (((Z.land ((V 36%nat) / 4294967296) 1610612736) - 1610612736) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb406c M) (st fx' R' 0xb4994 M')
        /\ (forall x, In x KS_adkD1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 1610612736
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 36%nat) / 4294967296)
        /\ bv_unsigned (getr R' (reg 14)) = (Z.land ((V 36%nat) / 4294967296) 1610612736)
        /\ (((Z.land ((V 36%nat) / 4294967296) 1610612736) - 1610612736) mod 2 ^ 64) < 1)).
Proof.
  intros wd2 wd33 wd34 wd35 wd36 wd38 wd50 r2 r8 r9 r10 r11 r18 r19 r20 r23 r24 r26 r27 r30
    rg2 al2 wr2 rg34 al34 dj34sh zs34 u35 u36 dj34sp rg33 rg38.
  set (val := fun j : nat => match j with
    | 2%nat | 33%nat | 34%nat | 35%nat | 36%nat | 38%nat | 50%nat => V j
    | k => bv_unsigned (getr R (reg k)) end).
  set (Ein := {| ev := fun j : nat => match j with
    | 2%nat | 33%nat | 34%nat | 35%nat | 36%nat | 38%nat | 50%nat => Z_to_bv 64 (V j)
    | k => getr R (reg k) end; eb := fun _ : nat => [] |}).
  assert (val_ok : forall j, bv_unsigned (ev Ein j) = val j).
  { intros j. unfold val, Ein. cbn [ev].
    do 51 (destruct j as [|j]; [lazy beta iota; first [reflexivity | apply BG.unsigned_lit; assumption] |]).
    reflexivity. }
  assert (regs_in : regs_ok Ein PadkD1.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. cbn [PadkD1.regs0 tl BG.slots].
    repeat (apply conj; [slotP val_ok|]). exact I. }
  assert (kn_in : know_ok RSEGS Ein M PadkD1.kn0).
  { unfold know_ok, PadkD1.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg2].
    - eapply L5K.kentry_KAlign; [evalEk val_ok (lazy beta iota) | lia | exact al2].
    - eapply L5K.kentry_KWr; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | | lazy beta iota; exactA wr2]; lazy beta iota; lia.
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg34].
    - eapply L5K.kentry_KAlign; [evalEk val_ok (lazy beta iota) | lia | exact al34].
    - eapply L5K.kentry_KDisj; [evalEk val_ok (lazy beta iota) .. | lazy beta iota; lia].
    - eapply L5KA.kentry_KZero; [evalEk val_ok (lazy beta iota; zfacts) | evalEk val_ok (lazy beta iota) | | | | lazy beta iota; exactA zs34];
        lazy beta iota; zfacts; lia.
    - eapply L5K.kentry_KWord8; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | lazy beta iota; exactA u35]; lazy beta iota; lia.
    - eapply L5K.kentry_KWord8; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | lazy beta iota; exactA u36]; lazy beta iota; lia.
    - eapply L5K.kentry_KDisj; [evalEk val_ok (lazy beta iota) .. | lazy beta iota; lia].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg33].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg38]. }
  destruct (PadkD1.seg_sound_ax fx Ein R M regs_in kn_in ltac:(constructor))
    as (fx1 & E1 & R1 & M1 & k & post & pick & agree & run & outs & _ & _ & frame & cells & grows).
  assert (same : forall a, M1 a = M a) by (intros a; apply frame, L5K.outside_nil_e).
  assert (d36 : bv_unsigned (ev E1 36) = V 36%nat).
  { change (ev E1 36) with (edenot E1 (EVar 36)). evalEk' val_ok agree (lazy beta iota). }
  cbn [PadkD1.PSS PadkD1.SXALL map app] in pick.
  exists fx1, R1, M1. split; [exact grows|]. split; [exact same|]. split; [intros i _; apply same|].
  destruct (L5K.nth_error_pair _ _ _ _ pick) as [[-> ->] | [-> ->]]; [left | right].
  all: cbn [SR.ps_pc SR.ps_regs SR.ps_cells PadkD1.ps0 PadkD1.ps1 PadkD1.cells0 PadkD1.cells1] in run, outs, cells.
  all: split; [exact run|].
  all: split; [eapply BG.kept_regs; [| exact regs_in | exact agree | exact outs]; first [exact KS_adkD1_0_ok | exact KS_adkD1_1_ok]|].
  all: repeat (split; [rewrite (BG.out_reg _ _ _ _ outs) by lia; L5K.norm_expr;
    first [ wordP' val_ok agree
          | evalEk' val_ok agree (zp_norm; pose proof (Z.mod_pos_bound (32768 * V 36%nat) 18446744073709551616 ltac:(lia)); zfacts)
          | cbn [edenot]; rewrite u_and64, u_srl64, d36, !BG.unsigned_lit by lia; reflexivity ]|]).
  all: pose proof (L5K.range_of_KRange _ _ _ _ _ _ _ (cells _ (or_introl eq_refl)) eq_refl) as flag;
    cbn [edenot] in flag; rewrite u_sltu64, u_sub64, u_and64, u_srl64, d36, !BG.unsigned_lit in flag by lia;
    revert flag; case Z.ltb_spec; intros c f; first [exact c | lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkD2 := LibSegBa_adkD2_b.
Definition KS_adkD2_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkD2.regs0 PadkD2.regs_out0).
Lemma KS_adkD2_0_ok : BG.kept_ok 80 PadkD2.regs0 PadkD2.regs_out0 KS_adkD2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkD2_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkD2.regs0 PadkD2.regs_out1).
Lemma KS_adkD2_1_ok : BG.kept_ok 80 PadkD2.regs0 PadkD2.regs_out1 KS_adkD2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkD2_2 : list nat := Eval vm_compute in (BG.kept_list 80 PadkD2.regs0 PadkD2.regs_out2).
Lemma KS_adkD2_2_ok : BG.kept_ok 80 PadkD2.regs0 PadkD2.regs_out2 KS_adkD2_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkD2_3 : list nat := Eval vm_compute in (BG.kept_list 80 PadkD2.regs0 PadkD2.regs_out3).
Lemma KS_adkD2_3_ok : BG.kept_ok 80 PadkD2.regs0 PadkD2.regs_out3 KS_adkD2_3 = true. Proof. vm_compute. reflexivity. Qed.
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
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 35%nat) / 4294967296)
        /\ getr R' (reg 14) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 2%nat) - 136)
        /\ getr R' (reg 16) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 39%nat) / 131072)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 35) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ ((((V 35%nat) / 4294967296) - 0) mod 2 ^ 64) < 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EVar 37)) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (EVar 36)) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) ((V 35%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 136) ((((16384 * (V 37%nat)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb40a4 M) (st fx' R' 0xb4164 M')
        /\ (forall x, In x KS_adkD2_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 50%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (((V 50%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) ((V 39%nat) / 131072)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 16383
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EVar 35) (ELit 0)) (ELit 0)) (ELit 1))) <= 0
        /\ ((((V 35%nat) / 4294967296) - 0) mod 2 ^ 64) < 1
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EVar 37)) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (EVar 36)) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) ((V 35%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 136) ((((16384 * (V 37%nat)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb40a4 M) (st fx' R' 0xb4164 M')
        /\ (forall x, In x KS_adkD2_2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 50%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (((V 50%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) ((V 39%nat) / 131072)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 16383
        /\ 1 <= ((((V 35%nat) / 4294967296) - 0) mod 2 ^ 64)
        /\ 1 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EVar 37)) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (EVar 36)) (ELit 0)) (ELit 0)) (ELit 1))) <= 1
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) ((V 35%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 136) ((((16384 * (V 37%nat)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64))
      \/ (msteps RSEGS (st fx R 0xb40a4 M) (st fx' R' 0xb4164 M')
        /\ (forall x, In x KS_adkD2_3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
        /\ getr R' (reg 10) = Z_to_bv 64 3
        /\ getr R' (reg 11) = Z_to_bv 64 18446744072850558976
        /\ getr R' (reg 12) = Z_to_bv 64 1000001536
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 35%nat) / 4294967296)
        /\ bv_unsigned (getr R' (reg 14)) = ((((16384 * (V 37%nat)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((V 50%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (((V 50%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 224) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 232) ((V 39%nat) / 131072)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 240) 16383
        /\ 0 <= bv_unsigned (edenot (Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | _ => getr R (reg j) end) (fun _ => [])) (EAlu Instr.ALU_SLTU (EAlu Instr.ALU_SUB (EAluw Instr.ALU_ADD (EAlu Instr.ALU_OR (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 16384) (EVar 37)) (EAlu Instr.ALU_AND (EVar 39) (ELit 16383))) (EVar 36)) (ELit 0)) (ELit 0)) (ELit 1))) <= 0
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 124) (V 35%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 128) ((V 35%nat) / 4294967296)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 132) (V 36%nat)
        /\ L5.u32_at RSEGS M' ((V 2%nat) - 136) ((((16384 * (V 37%nat)) mod 2 ^ 64) + (Z.land (V 39%nat) 16383)) mod 2 ^ 64))).
Proof.
  intros wd2 wd33 wd34 wd35 wd36 wd37 wd38 wd39 wd50 r2 r8 r9 r10 r11 r12 r13 r18 r19 r20 r23 r24 r26 r27 r30
    rg2 al2 wr2 img rg39 rg37 rg50 rg33 rg34 rg38.
  set (Ein := {| ev := fun j : nat => match j with
    | 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat)
    | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat)
    | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 50%nat => Z_to_bv 64 (V 50%nat)
    | _ => getr R (reg j) end; eb := fun _ : nat => [] |}).
  set (val := fun j : nat => match j with
    | 2%nat | 33%nat | 34%nat | 35%nat | 36%nat | 37%nat | 38%nat | 39%nat | 50%nat => V j
    | k => bv_unsigned (getr R (reg k)) end).
  assert (val_ok : forall j, bv_unsigned (ev Ein j) = val j).
  { intros j. unfold val, Ein. cbn [ev].
    do 51 (destruct j as [|j]; [lazy beta iota; first [reflexivity | apply BG.unsigned_lit; assumption] |]).
    reflexivity. }
  assert (regs_in : regs_ok Ein PadkD2.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. cbn [PadkD2.regs0 tl BG.slots].
    repeat (apply conj; [slotP val_ok|]). exact I. }
  assert (kn_in : know_ok RSEGS Ein M PadkD2.kn0).
  { unfold know_ok, PadkD2.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg2].
    - eapply L5K.kentry_KAlign; [evalEk val_ok (lazy beta iota) | lia | exact al2].
    - eapply L5K.kentry_KWr; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | | lazy beta iota; exactA wr2]; lazy beta iota; lia.
    - apply L5K.kentry_KImg; [lia | lia | exact img].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg39].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg37].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg50].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg33].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg34].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg38]. }
  destruct (PadkD2.seg_sound_ax fx Ein R M regs_in kn_in ltac:(constructor))
    as (fx1 & E1 & R1 & M1 & k & post & pick & agree & run & outs & _ & _ & frame & cells & grows).
  assert (keep : forall a : word, ~ (V 2%nat - 240 <= bv_unsigned a < V 2%nat - 240 + 64) ->
            ~ (V 2%nat - 168 <= bv_unsigned a < V 2%nat - 168 + 8) ->
            ~ (V 2%nat - 136 <= bv_unsigned a < V 2%nat - 136 + 16) -> M1 a = M a).
  { intros a o240 o168 o136. apply frame. cbn [PadkD2.F0].
    apply (L5K.outside_cons_e _ _ _ _ _ _ (V 2%nat) 64);
      [evalEk' val_ok agree (lazy beta iota) | evalEk' val_ok agree (lazy beta iota) | exact o240 |].
    apply (L5K.outside_cons_e _ _ _ _ _ _ (V 2%nat) 8);
      [evalEk' val_ok agree (lazy beta iota) | evalEk' val_ok agree (lazy beta iota) | exact o168 |].
    apply (L5K.outside_cons_e _ _ _ _ _ _ (V 2%nat) 16);
      [evalEk' val_ok agree (lazy beta iota) | evalEk' val_ok agree (lazy beta iota) | exact o136 |].
    apply L5K.outside_nil_e. }
  assert (d35 : bv_unsigned (ev E1 35) = V 35%nat).
  { change (ev E1 35) with (edenot E1 (EVar 35)). evalEk' val_ok agree (lazy beta iota). }
  assert (d37 : bv_unsigned (ev E1 37) = V 37%nat).
  { change (ev E1 37) with (edenot E1 (EVar 37)). evalEk' val_ok agree (lazy beta iota). }
  assert (d39 : bv_unsigned (ev E1 39) = V 39%nat).
  { change (ev E1 39) with (edenot E1 (EVar 39)). evalEk' val_ok agree (lazy beta iota). }
  exists fx1, R1, M1. split; [exact grows|]. split; [exact keep|].
  split. { intros i wi o240 o168 o136. apply keep; rewrite BG.unsigned_lit by exact wi; assumption. }
  cbn [PadkD2.PSS PadkD2.SXALL map app] in pick.
  destruct k as [|[|[|[|k]]]]; cbn [nth_error] in pick; [..|destruct k; discriminate].
  all: injection pick as <-.
  all: cbn [SR.ps_pc SR.ps_regs SR.ps_cells PadkD2.ps0 PadkD2.ps1 PadkD2.ps2 PadkD2.ps3
            PadkD2.cells0 PadkD2.cells1 PadkD2.cells2 PadkD2.cells3] in run, outs, cells.
  4: right; right; right. 3: right; right; left. 2: right; left. 1: left.
  all: pose proof (proj2 (Forall_forall _ _) cells) as cs;
    repeat (apply Forall_cons_iff in cs as [?c cs]).
  all: split; [exact run|].
  all: split; [eapply BG.kept_regs; [| exact regs_in | exact agree | exact outs];
    first [exact KS_adkD2_0_ok | exact KS_adkD2_1_ok | exact KS_adkD2_2_ok | exact KS_adkD2_3_ok]|].
  all: repeat (split; [rewrite (BG.out_reg _ _ _ _ outs) by lia; L5K.norm_expr;
    first [ wordP' val_ok agree
          | cbn [edenot]; rewrite u_add64, u_mul64, u_and64, d37, d39, !BG.unsigned_lit by lia; reflexivity ]|]).
  all: repeat match goal with |- ?x <= ?y /\ ?y <= ?z => fail 1 | |- _ /\ _ => split end.
  all: try match goal with c : kentry_ok _ _ _ (KWord _ 8 _) |- L5.u64_at _ _ _ _ =>
    eapply (u64_of_KWord8a _ _ _ _ _ _ _ _ c);
      [evalEk' val_ok agree (lazy beta iota) | evalEk' val_ok agree (lazy beta iota; zfacts) | lazy beta iota; lia] end.
  all: try match goal with c : kentry_ok _ _ _ (KWord _ 4 _) |- L5.u32_at _ _ _ _ =>
    eapply (u32_of_KWord4a _ _ _ _ _ _ _ _ c);
      [ evalEk' val_ok agree (lazy beta iota)
      | first [ evalEk' val_ok agree (lazy beta iota; zfacts)
              | cbn [edenot]; rewrite u_add64, u_mul64, u_and64, d37, d39, !BG.unsigned_lit by lia; reflexivity ]
      | lazy beta iota; lia ] end.
  all: try (rewrite (edenot_agree _ _ _ _ agree) by (vm_compute; reflexivity);
    match goal with c : kentry_ok _ _ _ (KRange ?e ?lo ?hi) |- ?lo <= bv_unsigned (edenot _ ?e) <= ?hi =>
      exact (L5K.range_of_KRange _ _ _ _ _ _ _ c eq_refl) end).
  all: match goal with c : kentry_ok _ _ _ (KRange (EAlu ALU_SLTU (EAlu ALU_SUB (EAlu ALU_SRL _ _) _) _) _ _) |- _ =>
      pose proof (L5K.range_of_KRange _ _ _ _ _ _ _ c eq_refl) as flag end;
    cbn [edenot] in flag; rewrite u_sltu64, u_sub64, u_srl64, d35, !BG.unsigned_lit in flag by lia;
    revert flag; case Z.ltb_spec; intros q f; first [exact q | lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkZ1 := LibSegBa_adkZ1_b.
Definition KS_adkZ1_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkZ1.regs0 PadkZ1.regs_out0).
Lemma KS_adkZ1_0_ok : BG.kept_ok 80 PadkZ1.regs0 PadkZ1.regs_out0 KS_adkZ1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkZ1_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkZ1.regs0 PadkZ1.regs_out1).
Lemma KS_adkZ1_1_ok : BG.kept_ok 80 PadkZ1.regs0 PadkZ1.regs_out1 KS_adkZ1_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkZ1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 32) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= ((V 38%nat) - (V 33%nat)) <= 1 -> L5.u32_at RSEGS M ((V 50%nat) + 32) (V 55%nat) -> 0 <= (V 55%nat) <= 9 ->
  L5.u64_at RSEGS M ((V 2%nat) - 240) 16383 -> L5.u64_at RSEGS M ((V 2%nat) - 232) (V 59%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 224) (V 38%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 216) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 208) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 200) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 184) (((V 50%nat) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) ((V 33%nat) + 42) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((V 50%nat) + 32) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb4268 M) (st fx' R' 0xb4564 M')
        /\ (forall x, In x KS_adkZ1_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 50%nat) + 36)
        /\ getr R' (reg 11) = Z_to_bv 64 18446744073709551611
        /\ getr R' (reg 13) = Z_to_bv 64 36
        /\ getr R' (reg 17) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ getr R' (reg 20) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 30) = Z_to_bv 64 (V 38%nat)
        /\ (((V 55%nat) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb4268 M) (st fx' R' 0xb4294 M')
        /\ (forall x, In x KS_adkZ1_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 5) = Z_to_bv 64 16383
        /\ getr R' (reg 10) = Z_to_bv 64 (V 55%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 36
        /\ getr R' (reg 17) = Z_to_bv 64 (V 59%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ getr R' (reg 20) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 30) = Z_to_bv 64 (V 38%nat)
        /\ 1 <= (((V 55%nat) - 0) mod 2 ^ 64))).
Proof.
  intros wd2 wd33 wd38 wd50 wd55 wd59 r2 r8 r9 r18 rg2 al2 wr2 rg50 rg33 rg38 u55 rg55
    u240 u232 u224 u216 u208 u200 u192 u184 u176 u168.
  set (val := fun j : nat => match j with
    | 2%nat | 33%nat | 38%nat | 50%nat | 55%nat | 59%nat => V j
    | k => bv_unsigned (getr R (reg k)) end).
  set (Ein := {| ev := fun j : nat => match j with
    | 2%nat | 33%nat | 38%nat | 50%nat | 55%nat | 59%nat => Z_to_bv 64 (V j)
    | k => getr R (reg k) end; eb := fun _ : nat => [] |}).
  assert (val_ok : forall j, bv_unsigned (ev Ein j) = val j).
  { intros j. unfold val, Ein. cbn [ev].
    do 60 (destruct j as [|j]; [lazy beta iota; first [reflexivity | apply BG.unsigned_lit; assumption] |]).
    reflexivity. }
  assert (regs_in : regs_ok Ein PadkZ1.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. cbn [PadkZ1.regs0 tl BG.slots].
    repeat (apply conj; [slotP val_ok|]). exact I. }
  assert (kn_in : know_ok RSEGS Ein M PadkZ1.kn0).
  { unfold know_ok, PadkZ1.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg2].
    - eapply L5K.kentry_KAlign; [evalEk val_ok (lazy beta iota) | lia | exact al2].
    - eapply L5K.kentry_KWr; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | | lazy beta iota; exactA wr2]; lazy beta iota; lia.
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg50].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg33].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg38].
    - eapply L5K.kentry_KWord4; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | lazy beta iota; exactA u55];
        lazy beta iota; lia.
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg55].
    - eapply L5K.kentry_KWord8; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | lazy beta iota; exactA u240]; lazy beta iota; lia.
    - eapply L5K.kentry_KWord8; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | lazy beta iota; exactA u232]; lazy beta iota; lia.
    - eapply L5K.kentry_KWord8; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | lazy beta iota; exactA u224]; lazy beta iota; lia.
    - eapply L5K.kentry_KWord8; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | lazy beta iota; exactA u216]; lazy beta iota; lia.
    - eapply L5K.kentry_KWord8; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | lazy beta iota; exactA u208]; lazy beta iota; lia.
    - eapply L5K.kentry_KWord8; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | lazy beta iota; exactA u200]; lazy beta iota; lia.
    - eapply L5K.kentry_KWord8; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | lazy beta iota; exactA u192]; lazy beta iota; lia.
    - eapply L5K.kentry_KWord8; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota; zfacts) | | | lazy beta iota; exactA u184]; lazy beta iota; lia.
    - eapply L5K.kentry_KWord8; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | lazy beta iota; exactA u176]; lazy beta iota; lia.
    - eapply L5K.kentry_KWord8; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | lazy beta iota; exactA u168]; lazy beta iota; lia. }
  destruct (PadkZ1.seg_sound_ax fx Ein R M regs_in kn_in ltac:(constructor))
    as (fx1 & E1 & R1 & M1 & k & post & pick & agree & run & outs & _ & _ & frame & cells & grows).
  assert (same : forall a, M1 a = M a) by (intros a; apply frame, L5K.outside_nil_e).
  assert (d55 : bv_unsigned (ev E1 55) = V 55%nat).
  { change (ev E1 55) with (edenot E1 (EVar 55)). evalEk' val_ok agree (lazy beta iota). }
  cbn [PadkZ1.PSS PadkZ1.SXALL map app] in pick.
  exists fx1, R1, M1. split; [exact grows|]. split; [exact same|]. split; [intros i _; apply same|].
  destruct (L5K.nth_error_pair _ _ _ _ pick) as [[-> ->] | [-> ->]]; [left | right].
  all: cbn [SR.ps_pc SR.ps_regs SR.ps_cells PadkZ1.ps0 PadkZ1.ps1 PadkZ1.cells0 PadkZ1.cells1] in run, outs, cells.
  all: split; [exact run|].
  all: split; [eapply BG.kept_regs; [| exact regs_in | exact agree | exact outs]; first [exact KS_adkZ1_0_ok | exact KS_adkZ1_1_ok]|].
  all: repeat (split; [rewrite (BG.out_reg _ _ _ _ outs) by lia; L5K.norm_expr; wordP' val_ok agree|]).
  all: pose proof (L5K.range_of_KRange _ _ _ _ _ _ _ (cells _ (or_introl eq_refl)) eq_refl) as flag;
    cbn [edenot] in flag; rewrite u_sltu64, u_sub64, d55, !BG.unsigned_lit in flag by lia;
    revert flag; case Z.ltb_spec; intros c f; first [exact c | lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkSC := LibSegBa_adkSC_b.
Definition KS_adkSC_0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkSC.regs0 PadkSC.regs_out0).
Lemma KS_adkSC_0_ok : BG.kept_ok 80 PadkSC.regs0 PadkSC.regs_out0 KS_adkSC_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_adkSC_1 : list nat := Eval vm_compute in (BG.kept_list 80 PadkSC.regs0 PadkSC.regs_out1).
Lemma KS_adkSC_1_ok : BG.kept_ok 80 PadkSC.regs0 PadkSC.regs_out1 KS_adkSC_1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkSC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 16383 -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 10) = Z_to_bv 64 (V 52%nat) -> getr R (reg 11) = Z_to_bv 64 18446744073709551611 -> getr R (reg 13) = Z_to_bv 64 (V 54%nat) -> getr R (reg 17) = Z_to_bv 64 (V 59%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 52%nat) - 4) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 30) = Z_to_bv 64 (V 38%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= ((V 38%nat) - (V 33%nat)) <= 1 -> 4096 <= (V 52%nat) <= 140737488355320 -> aligned (V 52%nat) 4 ->
  L5KA.zeros_at M (((V 52%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 52%nat) (V 53%nat) -> 0 <= (V 53%nat) <= 9 -> 2 <= (V 54%nat) <= 36 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ ((msteps RSEGS (st fx R 0xb4564 M) (st fx' R' 0xb4564 M')
        /\ (forall x, In x KS_adkSC_0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 52%nat) + 4)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 54%nat) - 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ (((V 53%nat) - 0) mod 2 ^ 64) < 1)
      \/ (msteps RSEGS (st fx R 0xb4564 M) (st fx' R' 0xb4294 M')
        /\ (forall x, In x KS_adkSC_1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 52%nat) + 4)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 54%nat) - 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ 1 <= (((V 53%nat) - 0) mod 2 ^ 64))).
Proof.
  intros wd2 wd33 wd38 wd50 wd52 wd53 wd54 wd59 r2 r5 r8 r9 r10 r11 r13 r17 r18 r19 r20 r23 r26 r30
    rg2 al2 wr2 rg50 rg33 rg38 rg52 al52 zs52 u52 rg53 rg54.
  set (val := fun j : nat => match j with
    | 2%nat | 33%nat | 38%nat | 50%nat | 52%nat | 53%nat | 54%nat | 59%nat => V j
    | k => bv_unsigned (getr R (reg k)) end).
  set (Ein := {| ev := fun j : nat => match j with
    | 2%nat | 33%nat | 38%nat | 50%nat | 52%nat | 53%nat | 54%nat | 59%nat => Z_to_bv 64 (V j)
    | k => getr R (reg k) end; eb := fun _ : nat => [] |}).
  assert (val_ok : forall j, bv_unsigned (ev Ein j) = val j).
  { intros j. unfold val, Ein. cbn [ev].
    do 60 (destruct j as [|j]; [lazy beta iota; first [reflexivity | apply BG.unsigned_lit; assumption] |]).
    reflexivity. }
  assert (regs_in : regs_ok Ein PadkSC.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. cbn [PadkSC.regs0 tl BG.slots].
    repeat (apply conj; [slotP val_ok|]). exact I. }
  assert (kn_in : know_ok RSEGS Ein M PadkSC.kn0).
  { unfold know_ok, PadkSC.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg2].
    - eapply L5K.kentry_KAlign; [evalEk val_ok (lazy beta iota) | lia | exact al2].
    - eapply L5K.kentry_KWr; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | | lazy beta iota; exactA wr2]; lazy beta iota; lia.
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg50].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg33].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg38].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg52].
    - eapply L5K.kentry_KAlign; [evalEk val_ok (lazy beta iota) | lia | exact al52].
    - eapply L5KA.kentry_KZero; [evalEk val_ok (lazy beta iota; zfacts) | evalEk val_ok (lazy beta iota) | | | | lazy beta iota; exactA zs52];
        lazy beta iota; zfacts; lia.
    - eapply L5K.kentry_KWord4; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | lazy beta iota; exactA u52];
        lazy beta iota; lia.
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg53].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg54]. }
  destruct (PadkSC.seg_sound_ax fx Ein R M regs_in kn_in ltac:(constructor))
    as (fx1 & E1 & R1 & M1 & k & post & pick & agree & run & outs & _ & _ & frame & cells & grows).
  assert (same : forall a, M1 a = M a) by (intros a; apply frame, L5K.outside_nil_e).
  assert (d53 : bv_unsigned (ev E1 53) = V 53%nat).
  { change (ev E1 53) with (edenot E1 (EVar 53)). evalEk' val_ok agree (lazy beta iota). }
  cbn [PadkSC.PSS PadkSC.SXALL map app] in pick.
  exists fx1, R1, M1. split; [exact grows|]. split; [exact same|]. split; [intros i _; apply same|].
  destruct (L5K.nth_error_pair _ _ _ _ pick) as [[-> ->] | [-> ->]]; [left | right].
  all: cbn [SR.ps_pc SR.ps_regs SR.ps_cells PadkSC.ps0 PadkSC.ps1 PadkSC.cells0 PadkSC.cells1] in run, outs, cells.
  all: split; [exact run|].
  all: split; [eapply BG.kept_regs; [| exact regs_in | exact agree | exact outs]; first [exact KS_adkSC_0_ok | exact KS_adkSC_1_ok]|].
  all: repeat (split; [rewrite (BG.out_reg _ _ _ _ outs) by lia; L5K.norm_expr; wordP' val_ok agree|]).
  all: pose proof (L5K.range_of_KRange _ _ _ _ _ _ _ (cells _ (or_introl eq_refl)) eq_refl) as flag;
    cbn [edenot] in flag; rewrite u_sltu64, u_sub64, d53, !BG.unsigned_lit in flag by lia;
    revert flag; case Z.ltb_spec; intros c f; first [exact c | lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PadkZ0 := LibSegBa_adkZ0_b.
Definition KS_adkZ0 : list nat := Eval vm_compute in (BG.kept_list 80 PadkZ0.regs0 PadkZ0.regs_out0).
Lemma KS_adkZ0_ok : BG.kept_ok 80 PadkZ0.regs0 PadkZ0.regs_out0 KS_adkZ0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma adkZ0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 59%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 5) = Z_to_bv 64 16383 -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 256) -> getr R (reg 17) = Z_to_bv 64 (V 59%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 50%nat) + 32) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 50%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 50%nat) -> getr R (reg 27) = Z_to_bv 64 (V 50%nat) -> getr R (reg 30) = Z_to_bv 64 (V 38%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 256) 256 -> 4096 <= (V 50%nat) <= 140737488354816 ->
  4096 <= (V 33%nat) <= 140737488355280 -> 0 <= ((V 38%nat) - (V 33%nat)) <= 1 -> 4096 <= (V 50%nat) <= 140737488354816 -> aligned (V 50%nat) 32 ->
  L5.writable RSEGS M (V 50%nat) 512 -> (2147446784 + 17592186048512 <= (V 50%nat) \/ (V 50%nat) + 512 <= 2147446784) -> (((V 2%nat) - 256) + 256 <= (V 50%nat) \/ (V 50%nat) + 512 <= ((V 2%nat) - 256)) -> (65536 + 6840320 <= (V 50%nat) \/ (V 50%nat) + 512 <= 65536) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 32) <= bv_unsigned a < ((V 50%nat) + 32) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 32) <= i < ((V 50%nat) + 32) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb425c M) (st fx' R' 0xb4294 M')
        /\ (forall x, In x KS_adkZ0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 25) = getr R (reg 25)
        /\ L5.u32_at RSEGS M' ((V 50%nat) + 32) 0).
Proof.
  intros wd2 wd33 wd38 wd50 wd59 r2 r5 r8 r9 r17 r18 r19 r20 r23 r26 r27 r30
    rg2 al2 wr2 rg50 rg33 rg38 rg50' al50 wr50 dj50sh dj50sp dj50img.
  set (val := fun j : nat => match j with
    | 2%nat | 33%nat | 38%nat | 50%nat | 59%nat => V j
    | k => bv_unsigned (getr R (reg k)) end).
  set (Ein := {| ev := fun j : nat => match j with
    | 2%nat | 33%nat | 38%nat | 50%nat | 59%nat => Z_to_bv 64 (V j)
    | k => getr R (reg k) end; eb := fun _ : nat => [] |}).
  assert (val_ok : forall j, bv_unsigned (ev Ein j) = val j).
  { intros j. unfold val, Ein. cbn [ev].
    do 60 (destruct j as [|j]; [lazy beta iota; first [reflexivity | apply BG.unsigned_lit; assumption] |]).
    reflexivity. }
  assert (regs_in : regs_ok Ein PadkZ0.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity|]. cbn [PadkZ0.regs0 tl BG.slots].
    repeat (apply conj; [slotP val_ok|]). exact I. }
  assert (kn_in : know_ok RSEGS Ein M PadkZ0.kn0).
  { unfold know_ok, PadkZ0.kn0. repeat apply Forall_cons; [..|apply Forall_nil].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg2].
    - eapply L5K.kentry_KAlign; [evalEk val_ok (lazy beta iota) | lia | exact al2].
    - eapply L5K.kentry_KWr; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | | lazy beta iota; exactA wr2]; lazy beta iota; lia.
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg50].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg33].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg38].
    - eapply L5K.kentry_KRange; [evalEk val_ok (lazy beta iota) | exact rg50'].
    - eapply L5K.kentry_KAlign; [evalEk val_ok (lazy beta iota) | lia | exact al50].
    - eapply L5K.kentry_KWr; [evalEk val_ok (lazy beta iota) | evalEk val_ok (lazy beta iota) | | | | lazy beta iota; exactA wr50]; lazy beta iota; lia.
    - eapply L5K.kentry_KDisj; [evalEk val_ok (lazy beta iota) .. | lazy beta iota; lia].
    - eapply L5K.kentry_KDisj; [evalEk val_ok (lazy beta iota) .. | lazy beta iota; lia].
    - eapply L5K.kentry_KDisj; [evalEk val_ok (lazy beta iota) .. | lazy beta iota; lia]. }
  destruct (PadkZ0.seg_sound_ax fx Ein R M regs_in kn_in ltac:(constructor))
    as (fx1 & E1 & R1 & M1 & k & post & pick & agree & run & outs & _ & _ & frame & cells & grows).
  cbn [PadkZ0.PSS PadkZ0.SXALL map app] in pick. apply L5K.nth_error_single in pick. subst post.
  cbn [SR.ps_pc SR.ps_regs SR.ps_cells PadkZ0.ps0 PadkZ0.cells0] in run, outs, cells.
  assert (keep : forall a : word, ~ (V 50%nat + 32 <= bv_unsigned a < V 50%nat + 32 + 4) -> M1 a = M a).
  { intros a off. apply frame. cbn [PadkZ0.F0].
    apply (L5K.outside_cons_e _ _ _ _ _ _ (V 50%nat) 4).
    - evalEk' val_ok agree (lazy beta iota).
    - evalEk' val_ok agree (lazy beta iota).
    - exact off.
    - apply L5K.outside_nil_e. }
  exists fx1, R1, M1.
  split; [exact grows|]. split; [exact keep|].
  split. { intros i wi off. apply keep. rewrite BG.unsigned_lit by exact wi. exact off. }
  split; [exact run|].
  split. { exact (BG.kept_regs _ _ _ _ _ _ _ _ KS_adkZ0_ok regs_in agree outs). }
  split. { rewrite (BG.out_reg _ _ _ 13 outs) by lia. reflexivity. }
  split. { apply (BG.kept_regs _ _ _ _ _ _ _ _ KS_adkZ0_ok regs_in agree outs). apply L5K.in_b. vm_compute. reflexivity. }
  apply (u32_of_KWord4a E1 M1 (EVar 50) 32 (ELit 0) (V 50%nat)).
  - apply cells. left. reflexivity.
  - evalEk' val_ok agree (lazy beta iota).
  - evalEk' val_ok agree (lazy beta iota).
  - reflexivity.
Qed.
(* [comment removed for export] *)

End PNADP2.
