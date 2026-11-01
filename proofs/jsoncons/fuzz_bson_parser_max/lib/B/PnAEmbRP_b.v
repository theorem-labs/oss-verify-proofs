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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.seg Require LibSegBa_azrE0_b LibSegBa_azrE1_b LibSegBa_azrE2_b LibSegBa_azrE3_b LibSegBa_azrF1_b LibSegBa_azrF2_b.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNAERP.
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
Module PazrE0 := LibSegBa_azrE0_b.
Definition KS_azrE0 : list nat := Eval vm_compute in (BG.kept_list 60 PazrE0.regs0 PazrE0.regs_out0).
Lemma KS_azrE0_ok : BG.kept_ok 60 PazrE0.regs0 PazrE0.regs_out0 KS_azrE0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azrE0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5.img_clear M 65536 1282048 ->
  L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) -> (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) ->
  L5.u64_at RSEGS M (V 33%nat) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 16) 0 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 192) <= bv_unsigned a < ((V 2%nat) - 192) + 192) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 192) <= i < ((V 2%nat) - 192) + 192) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad11c M) (st fx' R' 0x130338 M')
        /\ (forall x, In x KS_azrE0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710136
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 176)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 9) = Z_to_bv 64 1
        /\ getr R' (reg 10) = Z_to_bv 64 40
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 1309752
        /\ getr R' (reg 13) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 2147450880
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 709116
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)).
Proof.
  intros w2 w33 w34 w35 w52 x2v x10v x11v x12v x13v lim2 al2
    wrt1 img1 m64_1 m32_1 lim33 al33 sep1 shz1 sep2 sep3 m64_2 m64_3
    m64_4 shz2.
  unfold aligned in *.
  (* An index the statement names takes its value from V. Any other index j takes its value from
     getr R (reg j), and reg j wraps j modulo 32: an index of 32 or more reads register j mod 32. *)
  pose (vals := fun j : nat => match j with
                | 2%nat => V 2%nat
                | 33%nat => V 33%nat
                | 34%nat => V 34%nat
                | 35%nat => V 35%nat
                | 52%nat => V 52%nat
                | _ => bv_unsigned (getr R (reg j)) end).
  pose (Ein := {| ev := fun j : nat => match j with
                         | 2%nat => Z_to_bv 64 (V 2%nat)
                         | 33%nat => Z_to_bv 64 (V 33%nat)
                         | 34%nat => Z_to_bv 64 (V 34%nat)
                         | 35%nat => Z_to_bv 64 (V 35%nat)
                         | 52%nat => Z_to_bv 64 (V 52%nat)
                         | _ => getr R (reg j) end;
                  eb := fun _ : nat => [] |}).
  assert (valsOK : forall j, bv_unsigned (ev Ein j) = vals j).
  { intros j. unfold Ein, vals. cbn [ev].
    repeat match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n; cbv beta iota end.
    all: first [reflexivity | apply L5.unsigned_lit; assumption]. }
  assert (regsIn : regs_ok Ein PazrE0.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity |].
    unfold PazrE0.regs0. cbn [tl BG.slots].
    repeat match goal with |- _ /\ _ => split end.
    all: first [exact I | slotP valsOK]. }
  assert (knowIn : know_ok RSEGS Ein M PazrE0.kn0).
  { unfold know_ok, PazrE0.kn0.
    repeat apply Forall_cons; [.. | apply Forall_nil].
    (* The sep premises serve only the KDisj entries, so this line clears them from every other goal. *)
    all: lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => idtac | _ => clear sep1 sep2 sep3 end.
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim2].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al2].
    - eapply L5K.kentry_KWr; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA wrt1].
    - apply L5K.kentry_KImg; [lia | lia | exact img1].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_1].
    - eapply L5K.kentry_KWord4; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m32_1].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim33].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al33].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep1; lia].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz1].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep2; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep3; lia].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_2].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_3].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_4].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz2]. }
  clear sep1 sep2 sep3.
  destruct (PazrE0.seg_sound_ax fx Ein R M regsIn knowIn (Forall_nil _))
    as (fx' & Eout & R' & M' & idx & ps & sel & agrees & exec & regsOut & _ & _ & untouched & cellsOut & growM).
  change PazrE0.PSS with [PazrE0.ps0] in sel.
  apply L5K.nth_error_single in sel. subst ps.
  exists fx', R', M'.
  repeat match goal with |- _ /\ _ => split end.
  - exact growM.
  - intros a away1. apply untouched. unfold PazrE0.F0.
    repeat (eapply L5K.outside_cons_e;
            [evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | eassumption |]).
    apply L5K.outside_nil_e.
  - intros i iw away1. apply untouched. unfold PazrE0.F0.
    repeat (eapply L5K.outside_cons_e;
            [evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac
            | rewrite (L5.unsigned_lit i iw); eassumption |]).
    apply L5K.outside_nil_e.
  - exact exec.
  - exact (BG.kept_regs _ _ _ _ _ _ _ _ KS_azrE0_ok regsIn agrees regsOut).
  - rewrite (BG.out_reg _ _ _ 1 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 2 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 8 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 9 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 10 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 11 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 12 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 13 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 14 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 15 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 18 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 19 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 20 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 21 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 22 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - exact (BG.kept_regs _ _ _ _ _ _ _ _ KS_azrE0_ok regsIn agrees regsOut 23 (L5K.in_b 23 KS_azrE0 eq_refl)).
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 7 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 8 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 1 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 0 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 9 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 10 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 11 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 12 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 13 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 14 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 15 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 16 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 6 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 5 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 4 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 3 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE0.ps0) 2 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazrE1 := LibSegBa_azrE1_b.
Definition KS_azrE1 : list nat := Eval vm_compute in (BG.kept_list 60 PazrE1.regs0 PazrE1.regs_out0).
Lemma KS_azrE1_ok : BG.kept_ok 60 PazrE1.regs0 PazrE1.regs_out0 KS_azrE1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azrE1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 176) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 9) = Z_to_bv 64 1 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 19) = Z_to_bv 64 0 -> getr R (reg 20) = Z_to_bv 64 ((((V 2%nat) - 80) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 2147450880 -> getr R (reg 23) = Z_to_bv 64 (V 51%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 16) 0 ->
  6905856 <= (V 34%nat) <= 140737488355324 -> aligned (V 34%nat) 4 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 ->
  L5.u32_at RSEGS M (V 34%nat) (V 38%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 6905856 <= (V 35%nat) <= 140737488355324 ->
  aligned (V 35%nat) 4 -> (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 35%nat) (V 39%nat) ->
  (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 4 <= (V 33%nat)) -> 6905856 <= (V 52%nat) <= 140737488355324 -> aligned (V 52%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 52%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 4 <= (V 33%nat)) -> 0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 2147483647 -> 0 <= (V 53%nat) <= 2147483647 ->
  4096 <= (V 40%nat) <= 140737488355288 -> aligned (V 40%nat) 16 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 40 <= 2147446784) -> L5KA.zeros_at M (((V 40%nat) / 8) + 2147450880) 5 ->
  L5.writable RSEGS M (V 40%nat) 40 -> (((V 2%nat) - 4096) + 4096 <= (V 40%nat) \/ (V 40%nat) + 40 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 33%nat)) -> (65536 + 6840320 <= (V 40%nat) \/ (V 40%nat) + 40 <= 65536) ->
  ((V 34%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 34%nat)) -> ((V 35%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 35%nat)) -> ((V 52%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 120) 709116 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  L5.img_clear M 65536 1282048 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 256) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 256) -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad5f8 M) (st fx' R' 0x77c94 M')
        /\ (forall x, In x KS_azrE1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 710644
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 192)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 104)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 40
        /\ getr R' (reg 15) = Z_to_bv 64 1
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 33%nat) + 16) / 8)
        /\ getr R' (reg 17) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 2%nat) - 96)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) (V 52%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 709336
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 32) 0
        /\ L5.u8_at RSEGS M' ((V 40%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 16) (V 53%nat)
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 8) (V 39%nat)
        /\ L5.u32_at RSEGS M' (V 40%nat) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 40%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) ((V 40%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))).
Proof.
  intros w2 w33 w34 w35 w38 w39 w40 w43 w44 w45 w46 w47
    w48 w49 w50 w51 w52 w53 x2v x8v x9v x10v x18v x19v
    x20v x21v x22v x23v lim2 al2 wrt1 shz1 img1 m64_1 m32_1 lim33
    al33 sep1 shz2 sep2 sep3 m64_2 m64_3 m64_4 lim34 al34 sep4 shz3
    m32_2 sep5 sep6 lim35 al35 sep7 shz4 m32_3 sep8 sep9 lim52 al52
    sep10 shz5 m32_4 sep11 sep12 lim38 lim39 lim53 lim40 al40 sep13 shz6
    wrt2 sep14 sep15 sep16 sep17 sep18 sep19 m64_5 m64_6 m64_7 m64_8 m64_9
    m64_10 m64_11 m64_12 m64_13 m64_14 m64_15 m64_16 m64_17 m64_18 m64_19 m64_20 m64_21
    img2.
  unfold aligned in *.
  (* An index the statement names takes its value from V. Any other index j takes its value from
     getr R (reg j), and reg j wraps j modulo 32: an index of 32 or more reads register j mod 32. *)
  pose (vals := fun j : nat => match j with
                | 2%nat => V 2%nat
                | 33%nat => V 33%nat
                | 34%nat => V 34%nat
                | 35%nat => V 35%nat
                | 38%nat => V 38%nat
                | 39%nat => V 39%nat
                | 40%nat => V 40%nat
                | 43%nat => V 43%nat
                | 44%nat => V 44%nat
                | 45%nat => V 45%nat
                | 46%nat => V 46%nat
                | 47%nat => V 47%nat
                | 48%nat => V 48%nat
                | 49%nat => V 49%nat
                | 50%nat => V 50%nat
                | 51%nat => V 51%nat
                | 52%nat => V 52%nat
                | 53%nat => V 53%nat
                | _ => bv_unsigned (getr R (reg j)) end).
  pose (Ein := {| ev := fun j : nat => match j with
                         | 2%nat => Z_to_bv 64 (V 2%nat)
                         | 33%nat => Z_to_bv 64 (V 33%nat)
                         | 34%nat => Z_to_bv 64 (V 34%nat)
                         | 35%nat => Z_to_bv 64 (V 35%nat)
                         | 38%nat => Z_to_bv 64 (V 38%nat)
                         | 39%nat => Z_to_bv 64 (V 39%nat)
                         | 40%nat => Z_to_bv 64 (V 40%nat)
                         | 43%nat => Z_to_bv 64 (V 43%nat)
                         | 44%nat => Z_to_bv 64 (V 44%nat)
                         | 45%nat => Z_to_bv 64 (V 45%nat)
                         | 46%nat => Z_to_bv 64 (V 46%nat)
                         | 47%nat => Z_to_bv 64 (V 47%nat)
                         | 48%nat => Z_to_bv 64 (V 48%nat)
                         | 49%nat => Z_to_bv 64 (V 49%nat)
                         | 50%nat => Z_to_bv 64 (V 50%nat)
                         | 51%nat => Z_to_bv 64 (V 51%nat)
                         | 52%nat => Z_to_bv 64 (V 52%nat)
                         | 53%nat => Z_to_bv 64 (V 53%nat)
                         | _ => getr R (reg j) end;
                  eb := fun _ : nat => [] |}).
  assert (valsOK : forall j, bv_unsigned (ev Ein j) = vals j).
  { intros j. unfold Ein, vals. cbn [ev].
    repeat match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n; cbv beta iota end.
    all: first [reflexivity | apply L5.unsigned_lit; assumption]. }
  assert (regsIn : regs_ok Ein PazrE1.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity |].
    unfold PazrE1.regs0. cbn [tl BG.slots].
    repeat match goal with |- _ /\ _ => split end.
    all: first [exact I | slotP valsOK]. }
  assert (knowIn : know_ok RSEGS Ein M PazrE1.kn0).
  { unfold know_ok, PazrE1.kn0.
    repeat apply Forall_cons; [.. | apply Forall_nil].
    (* The sep premises serve only the KDisj entries, so this line clears them from every other goal. *)
    all: lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => idtac | _ => clear sep1 sep2 sep3 sep4 sep5 sep6 sep7 sep8 sep9 sep10 sep11 sep12 sep13 sep14 sep15 sep16 sep17 sep18 sep19 end.
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim2].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al2].
    - eapply L5K.kentry_KWr; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA wrt1].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz1].
    - apply L5K.kentry_KImg; [lia | lia | exact img1].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_1].
    - eapply L5K.kentry_KWord4; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m32_1].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim33].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al33].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep1; lia].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz2].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep2; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep3; lia].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_2].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_3].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_4].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim34].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al34].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep4; lia].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz3].
    - eapply L5K.kentry_KWord4; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m32_2].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep5; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep6; lia].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim35].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al35].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep7; lia].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz4].
    - eapply L5K.kentry_KWord4; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m32_3].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep8; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep9; lia].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim52].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al52].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep10; lia].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz5].
    - eapply L5K.kentry_KWord4; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m32_4].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep11; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep12; lia].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim38].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim39].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim53].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim40].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al40].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep13; lia].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz6].
    - eapply L5K.kentry_KWr; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA wrt2].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep14; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep15; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep16; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep17; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep18; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep19; lia].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_5].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_6].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_7].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_8].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_9].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_10].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_11].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_12].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_13].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_14].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_15].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_16].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_17].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_18].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_19].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_20].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_21].
    - apply L5K.kentry_KImg; [lia | lia | exact img2]. }
  clear sep1 sep2 sep3 sep4 sep5 sep6 sep7 sep8 sep9 sep10 sep11 sep12 sep13 sep14 sep15 sep16 sep17 sep18 sep19.
  destruct (PazrE1.seg_sound_ax fx Ein R M regsIn knowIn (Forall_nil _))
    as (fx' & Eout & R' & M' & idx & ps & sel & agrees & exec & regsOut & _ & _ & untouched & cellsOut & growM).
  change PazrE1.PSS with [PazrE1.ps0] in sel.
  apply L5K.nth_error_single in sel. subst ps.
  exists fx', R', M'.
  repeat match goal with |- _ /\ _ => split end.
  - exact growM.
  - intros a away1 away2. apply untouched. unfold PazrE1.F0.
    repeat (eapply L5K.outside_cons_e;
            [evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | eassumption |]).
    apply L5K.outside_nil_e.
  - intros i iw away1 away2. apply untouched. unfold PazrE1.F0.
    repeat (eapply L5K.outside_cons_e;
            [evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac
            | rewrite (L5.unsigned_lit i iw); eassumption |]).
    apply L5K.outside_nil_e.
  - exact exec.
  - exact (BG.kept_regs _ _ _ _ _ _ _ _ KS_azrE1_ok regsIn agrees regsOut).
  - rewrite (BG.out_reg _ _ _ 1 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 2 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 8 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 9 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 11 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 12 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 13 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 14 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 15 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 16 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 17 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 18 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 19 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 20 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 22 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 23 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 24 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 5 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 6 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 7 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 8 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 9 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 17 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 11 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u8_of_KWord1a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 12 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 13 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 14 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u32_of_KWord4a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 15 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 10 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 18 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 19 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 20 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 21 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 22 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 23 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 24 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 25 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 26 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 27 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 16 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 4 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 3 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 2 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 1 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE1.ps0) 0 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazrE2 := LibSegBa_azrE2_b.
Definition KS_azrE2 : list nat := Eval vm_compute in (BG.kept_list 60 PazrE2.regs0 PazrE2.regs_out0).
Lemma KS_azrE2_ok : BG.kept_ok 60 PazrE2.regs0 PazrE2.regs_out0 KS_azrE2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azrE2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 192) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) - 104) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 ((V 2%nat) - 96) -> getr R (reg 20) = Z_to_bv 64 (V 40%nat) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 23) = Z_to_bv 64 ((((V 2%nat) - 96) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 65536 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) 0 -> L5.u64_at RSEGS M ((V 33%nat) + 8) 0 ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) 0 -> 4096 <= (V 40%nat) <= 140737488355288 -> aligned (V 40%nat) 16 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 40 <= 2147446784) ->
  L5KA.zeros_at M (((V 40%nat) / 8) + 2147450880) 5 -> L5.writable RSEGS M (V 40%nat) 40 -> (((V 2%nat) - 4096) + 4096 <= (V 40%nat) \/ (V 40%nat) + 40 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 33%nat)) ->
  (65536 + 6840320 <= (V 40%nat) \/ (V 40%nat) + 40 <= 65536) -> ((V 34%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 34%nat)) -> ((V 35%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 35%nat)) -> ((V 52%nat) + 4 <= (V 40%nat) \/ (V 40%nat) + 40 <= (V 52%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) ((V 40%nat) + 40) -> L5.u64_at RSEGS M ((V 2%nat) - 88) ((V 40%nat) + 40) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 120) 709336 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.u64_at RSEGS M ((V 2%nat) - 136) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 144) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 152) (V 35%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 160) (V 34%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 168) ((((V 33%nat) + 8) / 8) + 2147450880) ->
  L5.u64_at RSEGS M ((V 2%nat) - 176) 2147450880 -> L5.u64_at RSEGS M ((V 2%nat) - 184) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 192) (V 24%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 256) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 24) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 256) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 24) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad7f4 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azrE2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 711480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) + 40)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 40%nat) + 40)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 40%nat) + 40)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 1
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 40%nat) + 40)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 2147450880
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) ((V 33%nat) + 8)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 709336
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) ((V 40%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) 0
        /\ L5.u64_at RSEGS M' (V 33%nat) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 43%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (V 45%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (V 46%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 48%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (V 49%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) 0).
Proof.
  intros w2 w24 w33 w34 w35 w40 w43 w44 w45 w46 w47 w48
    w49 w50 w51 w52 x2v x8v x9v x18v x19v x20v x21v x22v
    x23v x24v lim2 al2 wrt1 shz1 img1 m64_1 m32_1 lim33 al33 sep1
    shz2 sep2 sep3 wrt2 m64_2 m64_3 m64_4 lim40 al40 sep4 shz3 wrt3
    sep5 sep6 sep7 sep8 sep9 sep10 m64_5 m64_6 m64_7 m64_8 m64_9 m64_10
    m64_11 m64_12 m64_13 m64_14 m64_15 m64_16 m64_17 m64_18 m64_19 m64_20 m64_21 m64_22
    m64_23 m64_24 m64_25 m64_26 m64_27.
  unfold aligned in *.
  (* An index the statement names takes its value from V. Any other index j takes its value from
     getr R (reg j), and reg j wraps j modulo 32: an index of 32 or more reads register j mod 32. *)
  pose (vals := fun j : nat => match j with
                | 2%nat => V 2%nat
                | 24%nat => V 24%nat
                | 33%nat => V 33%nat
                | 34%nat => V 34%nat
                | 35%nat => V 35%nat
                | 40%nat => V 40%nat
                | 43%nat => V 43%nat
                | 44%nat => V 44%nat
                | 45%nat => V 45%nat
                | 46%nat => V 46%nat
                | 47%nat => V 47%nat
                | 48%nat => V 48%nat
                | 49%nat => V 49%nat
                | 50%nat => V 50%nat
                | 51%nat => V 51%nat
                | 52%nat => V 52%nat
                | _ => bv_unsigned (getr R (reg j)) end).
  pose (Ein := {| ev := fun j : nat => match j with
                         | 2%nat => Z_to_bv 64 (V 2%nat)
                         | 24%nat => Z_to_bv 64 (V 24%nat)
                         | 33%nat => Z_to_bv 64 (V 33%nat)
                         | 34%nat => Z_to_bv 64 (V 34%nat)
                         | 35%nat => Z_to_bv 64 (V 35%nat)
                         | 40%nat => Z_to_bv 64 (V 40%nat)
                         | 43%nat => Z_to_bv 64 (V 43%nat)
                         | 44%nat => Z_to_bv 64 (V 44%nat)
                         | 45%nat => Z_to_bv 64 (V 45%nat)
                         | 46%nat => Z_to_bv 64 (V 46%nat)
                         | 47%nat => Z_to_bv 64 (V 47%nat)
                         | 48%nat => Z_to_bv 64 (V 48%nat)
                         | 49%nat => Z_to_bv 64 (V 49%nat)
                         | 50%nat => Z_to_bv 64 (V 50%nat)
                         | 51%nat => Z_to_bv 64 (V 51%nat)
                         | 52%nat => Z_to_bv 64 (V 52%nat)
                         | _ => getr R (reg j) end;
                  eb := fun _ : nat => [] |}).
  assert (valsOK : forall j, bv_unsigned (ev Ein j) = vals j).
  { intros j. unfold Ein, vals. cbn [ev].
    repeat match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n; cbv beta iota end.
    all: first [reflexivity | apply L5.unsigned_lit; assumption]. }
  assert (regsIn : regs_ok Ein PazrE2.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity |].
    unfold PazrE2.regs0. cbn [tl BG.slots].
    repeat match goal with |- _ /\ _ => split end.
    all: first [exact I | slotP valsOK]. }
  assert (knowIn : know_ok RSEGS Ein M PazrE2.kn0).
  { unfold know_ok, PazrE2.kn0.
    repeat apply Forall_cons; [.. | apply Forall_nil].
    (* The sep premises serve only the KDisj entries, so this line clears them from every other goal. *)
    all: lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => idtac | _ => clear sep1 sep2 sep3 sep4 sep5 sep6 sep7 sep8 sep9 sep10 end.
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim2].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al2].
    - eapply L5K.kentry_KWr; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA wrt1].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz1].
    - apply L5K.kentry_KImg; [lia | lia | exact img1].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_1].
    - eapply L5K.kentry_KWord4; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m32_1].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim33].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al33].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep1; lia].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz2].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep2; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep3; lia].
    - eapply L5K.kentry_KWr; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA wrt2].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_2].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_3].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_4].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim40].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al40].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep4; lia].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz3].
    - eapply L5K.kentry_KWr; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA wrt3].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep5; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep6; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep7; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep8; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep9; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep10; lia].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_5].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_6].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_7].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_8].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_9].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_10].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_11].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_12].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_13].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_14].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_15].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_16].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_17].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_18].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_19].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_20].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_21].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_22].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_23].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_24].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_25].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_26].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_27]. }
  clear sep1 sep2 sep3 sep4 sep5 sep6 sep7 sep8 sep9 sep10.
  destruct (PazrE2.seg_sound_ax fx Ein R M regsIn knowIn (Forall_nil _))
    as (fx' & Eout & R' & M' & idx & ps & sel & agrees & exec & regsOut & _ & _ & untouched & cellsOut & growM).
  change PazrE2.PSS with [PazrE2.ps0] in sel.
  apply L5K.nth_error_single in sel. subst ps.
  exists fx', R', M'.
  repeat match goal with |- _ /\ _ => split end.
  - exact growM.
  - intros a away1 away2. apply untouched. unfold PazrE2.F0.
    repeat (eapply L5K.outside_cons_e;
            [evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | eassumption |]).
    apply L5K.outside_nil_e.
  - intros i iw away1 away2. apply untouched. unfold PazrE2.F0.
    repeat (eapply L5K.outside_cons_e;
            [evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac
            | rewrite (L5.unsigned_lit i iw); eassumption |]).
    apply L5K.outside_nil_e.
  - exact exec.
  - exact (BG.kept_regs _ _ _ _ _ _ _ _ KS_azrE2_ok regsIn agrees regsOut).
  - rewrite (BG.out_reg _ _ _ 1 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 2 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 5 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 8 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 10 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 11 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 12 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 13 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 14 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 15 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 16 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 17 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 18 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 19 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 20 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 21 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 22 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 23 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 24 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 0 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 1 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 5 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 4 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 7 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 6 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 2 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 8 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 9 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 10 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 11 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 12 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 13 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 14 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 15 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 16 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 17 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE2.ps0) 3 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazrE3 := LibSegBa_azrE3_b.
Definition KS_azrE3 : list nat := Eval vm_compute in (BG.kept_list 60 PazrE3.regs0 PazrE3.regs_out0).
Lemma KS_azrE3_ok : BG.kept_ok 60 PazrE3.regs0 PazrE3.regs_out0 KS_azrE3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azrE3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 9) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 (V 52%nat) -> getr R (reg 19) = Z_to_bv 64 (V 35%nat) -> getr R (reg 20) = Z_to_bv 64 (V 34%nat) -> getr R (reg 21) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 2147450880 -> getr R (reg 23) = Z_to_bv 64 (V 51%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 40%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 40%nat) + 40) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) ((V 40%nat) + 40) -> 4096 <= (V 40%nat) <= 140737488355248 -> aligned (V 40%nat) 16 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 48) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 49%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 33%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 88) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 96) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 104) 0 ->
  L5.u64_at RSEGS M ((V 2%nat) - 120) 709336 -> L5.u64_at RSEGS M ((V 2%nat) - 128) ((V 33%nat) + 8) -> L5.img_clear M 65536 1282048 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 256) <= bv_unsigned a < ((V 2%nat) - 256) + 256) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 256) <= i < ((V 2%nat) - 256) + 256) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xadb38 M) (st fx' R' 0xad314 M')
        /\ (forall x, In x KS_azrE3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 40%nat) + 40)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 72)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 2147450880
        /\ getr R' (reg 14) = Z_to_bv 64 (((V 2%nat) - 72) / 8)
        /\ getr R' (reg 15) = Z_to_bv 64 ((((V 2%nat) - 88) / 8) + 2147450880)
        /\ getr R' (reg 16) = Z_to_bv 64 0
        /\ getr R' (reg 17) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) ((V 40%nat) + 40)).
Proof.
  intros w2 w33 w34 w35 w40 w43 w44 w45 w46 w47 w48 w49
    w50 w51 w52 x2v x8v x9v x18v x19v x20v x21v x22v x23v
    lim2 al2 wrt1 shz1 img1 m64_1 m32_1 lim33 al33 sep1 shz2 sep2
    sep3 wrt2 m64_2 m64_3 m64_4 lim40 al40 m64_5 m64_6 m64_7 m64_8 m64_9
    m64_10 m64_11 m64_12 m64_13 m64_14 m64_15 m64_16 m64_17 m64_18 m64_19 img2.
  unfold aligned in *.
  (* An index the statement names takes its value from V. Any other index j takes its value from
     getr R (reg j), and reg j wraps j modulo 32: an index of 32 or more reads register j mod 32. *)
  pose (vals := fun j : nat => match j with
                | 2%nat => V 2%nat
                | 33%nat => V 33%nat
                | 34%nat => V 34%nat
                | 35%nat => V 35%nat
                | 40%nat => V 40%nat
                | 43%nat => V 43%nat
                | 44%nat => V 44%nat
                | 45%nat => V 45%nat
                | 46%nat => V 46%nat
                | 47%nat => V 47%nat
                | 48%nat => V 48%nat
                | 49%nat => V 49%nat
                | 50%nat => V 50%nat
                | 51%nat => V 51%nat
                | 52%nat => V 52%nat
                | _ => bv_unsigned (getr R (reg j)) end).
  pose (Ein := {| ev := fun j : nat => match j with
                         | 2%nat => Z_to_bv 64 (V 2%nat)
                         | 33%nat => Z_to_bv 64 (V 33%nat)
                         | 34%nat => Z_to_bv 64 (V 34%nat)
                         | 35%nat => Z_to_bv 64 (V 35%nat)
                         | 40%nat => Z_to_bv 64 (V 40%nat)
                         | 43%nat => Z_to_bv 64 (V 43%nat)
                         | 44%nat => Z_to_bv 64 (V 44%nat)
                         | 45%nat => Z_to_bv 64 (V 45%nat)
                         | 46%nat => Z_to_bv 64 (V 46%nat)
                         | 47%nat => Z_to_bv 64 (V 47%nat)
                         | 48%nat => Z_to_bv 64 (V 48%nat)
                         | 49%nat => Z_to_bv 64 (V 49%nat)
                         | 50%nat => Z_to_bv 64 (V 50%nat)
                         | 51%nat => Z_to_bv 64 (V 51%nat)
                         | 52%nat => Z_to_bv 64 (V 52%nat)
                         | _ => getr R (reg j) end;
                  eb := fun _ : nat => [] |}).
  assert (valsOK : forall j, bv_unsigned (ev Ein j) = vals j).
  { intros j. unfold Ein, vals. cbn [ev].
    repeat match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n; cbv beta iota end.
    all: first [reflexivity | apply L5.unsigned_lit; assumption]. }
  assert (regsIn : regs_ok Ein PazrE3.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity |].
    unfold PazrE3.regs0. cbn [tl BG.slots].
    repeat match goal with |- _ /\ _ => split end.
    all: first [exact I | slotP valsOK]. }
  assert (knowIn : know_ok RSEGS Ein M PazrE3.kn0).
  { unfold know_ok, PazrE3.kn0.
    repeat apply Forall_cons; [.. | apply Forall_nil].
    (* The sep premises serve only the KDisj entries, so this line clears them from every other goal. *)
    all: lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => idtac | _ => clear sep1 sep2 sep3 end.
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim2].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al2].
    - eapply L5K.kentry_KWr; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA wrt1].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz1].
    - apply L5K.kentry_KImg; [lia | lia | exact img1].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_1].
    - eapply L5K.kentry_KWord4; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m32_1].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim33].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al33].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep1; lia].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz2].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep2; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep3; lia].
    - eapply L5K.kentry_KWr; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA wrt2].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_2].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_3].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_4].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim40].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al40].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_5].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_6].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_7].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_8].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_9].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_10].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_11].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_12].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_13].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_14].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_15].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_16].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_17].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_18].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_19].
    - apply L5K.kentry_KImg; [lia | lia | exact img2]. }
  clear sep1 sep2 sep3.
  destruct (PazrE3.seg_sound_ax fx Ein R M regsIn knowIn (Forall_nil _))
    as (fx' & Eout & R' & M' & idx & ps & sel & agrees & exec & regsOut & _ & _ & untouched & cellsOut & growM).
  change PazrE3.PSS with [PazrE3.ps0] in sel.
  apply L5K.nth_error_single in sel. subst ps.
  exists fx', R', M'.
  repeat match goal with |- _ /\ _ => split end.
  - exact growM.
  - intros a away1 away2. apply untouched. unfold PazrE3.F0.
    repeat (eapply L5K.outside_cons_e;
            [evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | eassumption |]).
    apply L5K.outside_nil_e.
  - intros i iw away1 away2. apply untouched. unfold PazrE3.F0.
    repeat (eapply L5K.outside_cons_e;
            [evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac
            | rewrite (L5.unsigned_lit i iw); eassumption |]).
    apply L5K.outside_nil_e.
  - exact exec.
  - exact (BG.kept_regs _ _ _ _ _ _ _ _ KS_azrE3_ok regsIn agrees regsOut).
  - rewrite (BG.out_reg _ _ _ 1 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 2 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 8 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 9 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 10 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 11 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 12 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 13 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 14 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 15 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 16 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 17 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 18 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 19 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 20 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 21 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 22 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 23 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrE3.ps0) 0 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazrF1 := LibSegBa_azrF1_b.
Definition KS_azrF1 : list nat := Eval vm_compute in (BG.kept_list 60 PazrF1.regs0 PazrF1.regs_out0).
Lemma KS_azrF1_ok : BG.kept_ok 60 PazrF1.regs0 PazrF1.regs_out0 KS_azrF1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azrF1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 (V 35%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + (V 37%nat)) -> L5.u64_at RSEGS M ((V 33%nat) + 16) (V 41%nat) ->
  4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 0 <= (V 37%nat) <= 81880 -> aligned (V 37%nat) 8 ->
  4136 <= (V 41%nat) <= 140737488355327 -> 40 <= ((V 41%nat) - ((V 36%nat) + (V 37%nat))) <= 81920 -> 0 <= ((V 41%nat) - (V 36%nat)) <= 163840 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xacf40 M) (st fx' R' 0x7ba7c M')
        /\ (forall x, In x KS_azrF1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 709968
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 80)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 36%nat) + (V 37%nat))
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + (V 37%nat)) + 40)
        /\ getr R' (reg 14) = Z_to_bv 64 1
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 36%nat) + (V 37%nat)) + 40)
        /\ getr R' (reg 17) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ getr R' (reg 20) = getr R (reg 20)
        /\ getr R' (reg 21) = getr R (reg 21)
        /\ getr R' (reg 22) = getr R (reg 22)
        /\ getr R' (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) 708524
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) ((V 36%nat) + (V 37%nat))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (((V 36%nat) + (V 37%nat)) + 40)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (V 52%nat)).
Proof.
  intros w2 w33 w34 w35 w36 w37 w41 w52 x2v x10v x11v x12v
    x13v lim2 al2 wrt1 shz1 img1 m64_1 m32_1 lim33 al33 sep1 shz2
    sep2 sep3 m64_2 m64_3 m64_4 lim36 al36 lim37 al37 lim41 limx1 limx2.
  unfold aligned in *.
  (* An index the statement names takes its value from V. Any other index j takes its value from
     getr R (reg j), and reg j wraps j modulo 32: an index of 32 or more reads register j mod 32. *)
  pose (vals := fun j : nat => match j with
                | 2%nat => V 2%nat
                | 33%nat => V 33%nat
                | 34%nat => V 34%nat
                | 35%nat => V 35%nat
                | 36%nat => V 36%nat
                | 37%nat => V 37%nat
                | 41%nat => V 41%nat
                | 52%nat => V 52%nat
                | _ => bv_unsigned (getr R (reg j)) end).
  pose (Ein := {| ev := fun j : nat => match j with
                         | 2%nat => Z_to_bv 64 (V 2%nat)
                         | 33%nat => Z_to_bv 64 (V 33%nat)
                         | 34%nat => Z_to_bv 64 (V 34%nat)
                         | 35%nat => Z_to_bv 64 (V 35%nat)
                         | 36%nat => Z_to_bv 64 (V 36%nat)
                         | 37%nat => Z_to_bv 64 (V 37%nat)
                         | 41%nat => Z_to_bv 64 (V 41%nat)
                         | 52%nat => Z_to_bv 64 (V 52%nat)
                         | _ => getr R (reg j) end;
                  eb := fun _ : nat => [] |}).
  assert (valsOK : forall j, bv_unsigned (ev Ein j) = vals j).
  { intros j. unfold Ein, vals. cbn [ev].
    repeat match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n; cbv beta iota end.
    all: first [reflexivity | apply L5.unsigned_lit; assumption]. }
  assert (regsIn : regs_ok Ein PazrF1.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity |].
    unfold PazrF1.regs0. cbn [tl BG.slots].
    repeat match goal with |- _ /\ _ => split end.
    all: first [exact I | slotP valsOK]. }
  assert (knowIn : know_ok RSEGS Ein M PazrF1.kn0).
  { unfold know_ok, PazrF1.kn0.
    repeat apply Forall_cons; [.. | apply Forall_nil].
    (* The sep premises serve only the KDisj entries, so this line clears them from every other goal. *)
    all: lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => idtac | _ => clear sep1 sep2 sep3 end.
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim2].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al2].
    - eapply L5K.kentry_KWr; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA wrt1].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz1].
    - apply L5K.kentry_KImg; [lia | lia | exact img1].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_1].
    - eapply L5K.kentry_KWord4; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m32_1].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim33].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al33].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep1; lia].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz2].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep2; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep3; lia].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_2].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_3].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_4].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim36].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al36].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim37].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al37].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim41].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact limx1].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact limx2]. }
  clear sep1 sep2 sep3.
  destruct (PazrF1.seg_sound_ax fx Ein R M regsIn knowIn (Forall_nil _))
    as (fx' & Eout & R' & M' & idx & ps & sel & agrees & exec & regsOut & _ & _ & untouched & cellsOut & growM).
  change PazrF1.PSS with [PazrF1.ps0] in sel.
  apply L5K.nth_error_single in sel. subst ps.
  exists fx', R', M'.
  repeat match goal with |- _ /\ _ => split end.
  - exact growM.
  - intros a away1. apply untouched. unfold PazrF1.F0.
    repeat (eapply L5K.outside_cons_e;
            [evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | eassumption |]).
    apply L5K.outside_nil_e.
  - intros i iw away1. apply untouched. unfold PazrF1.F0.
    repeat (eapply L5K.outside_cons_e;
            [evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac
            | rewrite (L5.unsigned_lit i iw); eassumption |]).
    apply L5K.outside_nil_e.
  - exact exec.
  - exact (BG.kept_regs _ _ _ _ _ _ _ _ KS_azrF1_ok regsIn agrees regsOut).
  - rewrite (BG.out_reg _ _ _ 1 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 2 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 8 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 9 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 10 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 11 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 12 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 13 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 14 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 15 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 16 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 17 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 18 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 19 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - exact (BG.kept_regs _ _ _ _ _ _ _ _ KS_azrF1_ok regsIn agrees regsOut 20 (L5K.in_b 20 KS_azrF1 eq_refl)).
  - exact (BG.kept_regs _ _ _ _ _ _ _ _ KS_azrF1_ok regsIn agrees regsOut 21 (L5K.in_b 21 KS_azrF1 eq_refl)).
  - exact (BG.kept_regs _ _ _ _ _ _ _ _ KS_azrF1_ok regsIn agrees regsOut 22 (L5K.in_b 22 KS_azrF1 eq_refl)).
  - exact (BG.kept_regs _ _ _ _ _ _ _ _ KS_azrF1_ok regsIn agrees regsOut 23 (L5K.in_b 23 KS_azrF1 eq_refl)).
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF1.ps0) 1 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF1.ps0) 4 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF1.ps0) 3 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF1.ps0) 2 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF1.ps0) 5 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF1.ps0) 6 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF1.ps0) 7 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF1.ps0) 8 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF1.ps0) 9 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF1.ps0) 0 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PazrF2 := LibSegBa_azrF2_b.
Definition KS_azrF2 : list nat := Eval vm_compute in (BG.kept_list 60 PazrF2.regs0 PazrF2.regs_out0).
Lemma KS_azrF2_ok : BG.kept_ok 60 PazrF2.regs0 PazrF2.regs_out0 KS_azrF2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma azrF2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 80) -> getr R (reg 8) = Z_to_bv 64 (V 52%nat) -> getr R (reg 9) = Z_to_bv 64 (V 35%nat) -> getr R (reg 18) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 (V 48%nat) -> getr R (reg 21) = Z_to_bv 64 (V 49%nat) -> getr R (reg 22) = Z_to_bv 64 (V 50%nat) -> getr R (reg 23) = Z_to_bv 64 (V 51%nat) ->
  140735332491264 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 4096) 4096 -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450368) 512 ->
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> 6905856 <= (V 33%nat) <= 140737488355295 ->
  aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 24 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 3 -> (((V 2%nat) - 4096) + 4096 <= (V 33%nat) \/ (V 33%nat) + 24 <= ((V 2%nat) - 4096)) ->
  (65536 + 6840320 <= (V 33%nat) \/ (V 33%nat) + 24 <= 65536) -> L5.writable RSEGS M (V 33%nat) 24 -> L5.u64_at RSEGS M (V 33%nat) (V 36%nat) -> L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 36%nat) + (V 37%nat)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 16) (V 41%nat) -> 4096 <= (V 36%nat) <= 140737488355288 -> aligned (V 36%nat) 16 -> 6905856 <= (V 34%nat) <= 140737488355324 ->
  aligned (V 34%nat) 4 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 34%nat) (V 38%nat) ->
  (((V 2%nat) - 4096) + 4096 <= (V 34%nat) \/ (V 34%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 34%nat) \/ (V 34%nat) + 4 <= (V 33%nat)) -> 6905856 <= (V 35%nat) <= 140737488355324 -> aligned (V 35%nat) 4 ->
  (2147446784 + 17592186048512 <= (V 35%nat) \/ (V 35%nat) + 4 <= 2147446784) -> L5KA.zeros_at M (((V 35%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 35%nat) (V 39%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 35%nat) \/ (V 35%nat) + 4 <= ((V 2%nat) - 4096)) ->
  ((V 33%nat) + 24 <= (V 35%nat) \/ (V 35%nat) + 4 <= (V 33%nat)) -> 6905856 <= (V 52%nat) <= 140737488355324 -> aligned (V 52%nat) 4 -> (2147446784 + 17592186048512 <= (V 52%nat) \/ (V 52%nat) + 4 <= 2147446784) ->
  L5KA.zeros_at M (((V 52%nat) / 8) + 2147450880) 1 -> L5.u32_at RSEGS M (V 52%nat) (V 53%nat) -> (((V 2%nat) - 4096) + 4096 <= (V 52%nat) \/ (V 52%nat) + 4 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= (V 52%nat) \/ (V 52%nat) + 4 <= (V 33%nat)) ->
  0 <= (V 38%nat) <= 2147483647 -> 0 <= (V 39%nat) <= 2147483647 -> 0 <= (V 53%nat) <= 2147483647 -> 0 <= (V 37%nat) <= 81880 ->
  aligned (V 37%nat) 8 -> 4136 <= (V 41%nat) <= 140737488355327 -> 40 <= ((V 41%nat) - ((V 36%nat) + (V 37%nat))) <= 81920 -> L5KA.zeros_at M ((((V 36%nat) + (V 37%nat)) / 8) + 2147450880) 5 ->
  L5.writable RSEGS M ((V 36%nat) + (V 37%nat)) 40 -> (2147446784 + 17592186048512 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 40 <= 2147446784) -> (65536 + 6840320 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 40 <= 65536) -> 4096 <= ((V 36%nat) + (V 37%nat)) <= 140737488355288 ->
  (((V 2%nat) - 4096) + 4096 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 40 <= ((V 2%nat) - 4096)) -> ((V 33%nat) + 24 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 40 <= (V 33%nat)) -> ((V 34%nat) + 4 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 40 <= (V 34%nat)) -> ((V 35%nat) + 4 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 40 <= (V 35%nat)) ->
  ((V 52%nat) + 4 <= ((V 36%nat) + (V 37%nat)) \/ ((V 36%nat) + (V 37%nat)) + 40 <= (V 52%nat)) -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 32) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (((V 36%nat) + (V 37%nat)) + 40) -> L5.u64_at RSEGS M ((V 2%nat) - 56) ((V 36%nat) + (V 37%nat)) ->
  L5.u64_at RSEGS M ((V 2%nat) - 64) (V 33%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) 708524 -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 52%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 36%nat) + (V 37%nat)) + 0) <= bv_unsigned a < (((V 36%nat) + (V 37%nat)) + 0) + 40) -> ~ (((V 33%nat) + 8) <= bv_unsigned a < ((V 33%nat) + 8) + 8) -> ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 36%nat) + (V 37%nat)) + 0) <= i < (((V 36%nat) + (V 37%nat)) + 0) + 40) -> ~ (((V 33%nat) + 8) <= i < ((V 33%nat) + 8) + 8) -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xad550 M) (st fx' R' 0xad09c M')
        /\ (forall x, In x KS_azrF2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (((V 36%nat) + (V 37%nat)) + 40)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 36%nat) + (V 37%nat)) + 40)
        /\ getr R' (reg 14) = Z_to_bv 64 2147450880
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 51%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (((V 36%nat) + (V 37%nat)) + 40)
        /\ L5.u64_at RSEGS M' (((V 36%nat) + (V 37%nat)) + 32) 0
        /\ L5.u8_at RSEGS M' (((V 36%nat) + (V 37%nat)) + 24) 0
        /\ L5.u64_at RSEGS M' (((V 36%nat) + (V 37%nat)) + 16) (V 53%nat)
        /\ L5.u64_at RSEGS M' (((V 36%nat) + (V 37%nat)) + 8) (V 39%nat)
        /\ L5.u32_at RSEGS M' ((V 36%nat) + (V 37%nat)) (V 38%nat)).
Proof.
  intros w2 w33 w34 w35 w36 w37 w38 w39 w41 w43 w44 w45
    w46 w47 w48 w49 w50 w51 w52 w53 x2v x8v x9v x18v
    x19v x20v x21v x22v x23v lim2 al2 wrt1 shz1 img1 m64_1 m32_1
    lim33 al33 sep1 shz2 sep2 sep3 wrt2 m64_2 m64_3 m64_4 lim36 al36
    lim34 al34 sep4 shz3 m32_2 sep5 sep6 lim35 al35 sep7 shz4 m32_3
    sep8 sep9 lim52 al52 sep10 shz5 m32_4 sep11 sep12 lim38 lim39 lim53
    lim37 al37 lim41 limx1 shz6 wrt3 sep13 sep14 limx2 sep15 sep16 sep17
    sep18 sep19 m64_5 m64_6 m64_7 m64_8 m64_9 m64_10 m64_11 m64_12 m64_13 m64_14.
  unfold aligned in *.
  (* An index the statement names takes its value from V. Any other index j takes its value from
     getr R (reg j), and reg j wraps j modulo 32: an index of 32 or more reads register j mod 32. *)
  pose (vals := fun j : nat => match j with
                | 2%nat => V 2%nat
                | 33%nat => V 33%nat
                | 34%nat => V 34%nat
                | 35%nat => V 35%nat
                | 36%nat => V 36%nat
                | 37%nat => V 37%nat
                | 38%nat => V 38%nat
                | 39%nat => V 39%nat
                | 41%nat => V 41%nat
                | 43%nat => V 43%nat
                | 44%nat => V 44%nat
                | 45%nat => V 45%nat
                | 46%nat => V 46%nat
                | 47%nat => V 47%nat
                | 48%nat => V 48%nat
                | 49%nat => V 49%nat
                | 50%nat => V 50%nat
                | 51%nat => V 51%nat
                | 52%nat => V 52%nat
                | 53%nat => V 53%nat
                | _ => bv_unsigned (getr R (reg j)) end).
  pose (Ein := {| ev := fun j : nat => match j with
                         | 2%nat => Z_to_bv 64 (V 2%nat)
                         | 33%nat => Z_to_bv 64 (V 33%nat)
                         | 34%nat => Z_to_bv 64 (V 34%nat)
                         | 35%nat => Z_to_bv 64 (V 35%nat)
                         | 36%nat => Z_to_bv 64 (V 36%nat)
                         | 37%nat => Z_to_bv 64 (V 37%nat)
                         | 38%nat => Z_to_bv 64 (V 38%nat)
                         | 39%nat => Z_to_bv 64 (V 39%nat)
                         | 41%nat => Z_to_bv 64 (V 41%nat)
                         | 43%nat => Z_to_bv 64 (V 43%nat)
                         | 44%nat => Z_to_bv 64 (V 44%nat)
                         | 45%nat => Z_to_bv 64 (V 45%nat)
                         | 46%nat => Z_to_bv 64 (V 46%nat)
                         | 47%nat => Z_to_bv 64 (V 47%nat)
                         | 48%nat => Z_to_bv 64 (V 48%nat)
                         | 49%nat => Z_to_bv 64 (V 49%nat)
                         | 50%nat => Z_to_bv 64 (V 50%nat)
                         | 51%nat => Z_to_bv 64 (V 51%nat)
                         | 52%nat => Z_to_bv 64 (V 52%nat)
                         | 53%nat => Z_to_bv 64 (V 53%nat)
                         | _ => getr R (reg j) end;
                  eb := fun _ : nat => [] |}).
  assert (valsOK : forall j, bv_unsigned (ev Ein j) = vals j).
  { intros j. unfold Ein, vals. cbn [ev].
    repeat match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n; cbv beta iota end.
    all: first [reflexivity | apply L5.unsigned_lit; assumption]. }
  assert (regsIn : regs_ok Ein PazrF2.regs0 R).
  { apply BG.regs_ok_of_slots; [reflexivity |].
    unfold PazrF2.regs0. cbn [tl BG.slots].
    repeat match goal with |- _ /\ _ => split end.
    all: first [exact I | slotP valsOK]. }
  assert (knowIn : know_ok RSEGS Ein M PazrF2.kn0).
  { unfold know_ok, PazrF2.kn0.
    repeat apply Forall_cons; [.. | apply Forall_nil].
    (* The sep premises serve only the KDisj entries, so this line clears them from every other goal. *)
    all: lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => idtac | _ => clear sep1 sep2 sep3 sep4 sep5 sep6 sep7 sep8 sep9 sep10 sep11 sep12 sep13 sep14 sep15 sep16 sep17 sep18 sep19 end.
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim2].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al2].
    - eapply L5K.kentry_KWr; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA wrt1].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz1].
    - apply L5K.kentry_KImg; [lia | lia | exact img1].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_1].
    - eapply L5K.kentry_KWord4; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m32_1].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim33].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al33].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep1; lia].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz2].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep2; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep3; lia].
    - eapply L5K.kentry_KWr; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA wrt2].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_2].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_3].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_4].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim36].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al36].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim34].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al34].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep4; lia].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz3].
    - eapply L5K.kentry_KWord4; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m32_2].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep5; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep6; lia].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim35].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al35].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep7; lia].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz4].
    - eapply L5K.kentry_KWord4; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m32_3].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep8; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep9; lia].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim52].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al52].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep10; lia].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz5].
    - eapply L5K.kentry_KWord4; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m32_4].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep11; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep12; lia].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim38].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim39].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim53].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim37].
    - eapply L5K.kentry_KAlign; [evalEk valsOK (zp_norm; zfacts) | lia | exact al37].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact lim41].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact limx1].
    - eapply L5KA.kentry_KZero; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA shz6].
    - eapply L5K.kentry_KWr; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | lia | zp_norm; zfacts; lia | exactA wrt3].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep13; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep14; lia].
    - eapply L5K.kentry_KRange; [evalEk valsOK (zp_norm; zfacts) | exact limx2].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep15; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep16; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep17; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep18; lia].
    - eapply L5K.kentry_KDisj; [(evalEk valsOK (zp_norm; zfacts)) .. | clear - sep19; lia].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_5].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_6].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_7].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_8].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_9].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_10].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_11].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_12].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_13].
    - eapply L5K.kentry_KWord8; [evalEk valsOK (zp_norm; zfacts) | evalEk valsOK (zp_norm; zfacts) | zp_norm; zfacts; lia | zp_norm; zfacts; lia | exactA m64_14]. }
  clear sep1 sep2 sep3 sep4 sep5 sep6 sep7 sep8 sep9 sep10 sep11 sep12 sep13 sep14 sep15 sep16 sep17 sep18 sep19.
  destruct (PazrF2.seg_sound_ax fx Ein R M regsIn knowIn (Forall_nil _))
    as (fx' & Eout & R' & M' & idx & ps & sel & agrees & exec & regsOut & _ & _ & untouched & cellsOut & growM).
  change PazrF2.PSS with [PazrF2.ps0] in sel.
  apply L5K.nth_error_single in sel. subst ps.
  exists fx', R', M'.
  repeat match goal with |- _ /\ _ => split end.
  - exact growM.
  - intros a away1 away2 away3. apply untouched. unfold PazrF2.F0.
    repeat (eapply L5K.outside_cons_e;
            [evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | eassumption |]).
    apply L5K.outside_nil_e.
  - intros i iw away1 away2 away3. apply untouched. unfold PazrF2.F0.
    repeat (eapply L5K.outside_cons_e;
            [evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac
            | rewrite (L5.unsigned_lit i iw); eassumption |]).
    apply L5K.outside_nil_e.
  - exact exec.
  - exact (BG.kept_regs _ _ _ _ _ _ _ _ KS_azrF2_ok regsIn agrees regsOut).
  - rewrite (BG.out_reg _ _ _ 1 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 2 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 8 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 9 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 10 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 11 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 12 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 13 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 14 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 15 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 18 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 19 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 20 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 21 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 22 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - rewrite (BG.out_reg _ _ _ 23 regsOut ltac:(lia)). L5K.norm_expr. wordP' valsOK agrees.
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF2.ps0) 0 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF2.ps0) 1 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u8_of_KWord1a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF2.ps0) 2 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF2.ps0) 3 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u64_of_KWord8a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF2.ps0) 4 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
  - eapply u32_of_KWord4a; [exact (cellsOut _ (nth_error_In (SR.ps_cells PazrF2.ps0) 5 eq_refl)) | evalEk' valsOK agrees idtac | evalEk' valsOK agrees idtac | lia].
Qed.
(* [comment removed for export] *)

End PNAERP.
