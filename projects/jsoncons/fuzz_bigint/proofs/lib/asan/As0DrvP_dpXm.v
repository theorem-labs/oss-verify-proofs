(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigLinkZA.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan As0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegZ_dpXm.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module AS0DRVP_dpXm.
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)).

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
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; reflexivity | solve_modk k ].
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
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].
(* [comment removed for export] *)
Module PdpXm := LibSegZ_dpXm.
Definition KS_dpXm : list nat := Eval vm_compute in (BG.kept_list 56 PdpXm.regs0 PdpXm.regs_out0).
Lemma KS_dpXm_ok : BG.kept_ok 56 PdpXm.regs0 PdpXm.regs_out0 KS_dpXm = true. Proof. vm_compute. reflexivity. Qed.
Lemma dpXm_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 4) = Z_to_bv 64 6360328 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 320) 320 -> L5.defined M ((V 2%nat) - 320) 320 ->
  L5.img_clear M 65536 880640 -> L5.writable RSEGS M 894080 8 -> L5.writable RSEGS M 894160 1 -> L5.writable RSEGS M 898032 8 ->
  L5.writable RSEGS M 6491480 1 -> L5.writable RSEGS M 6491488 4 -> L5.writable RSEGS M 6491496 8 -> L5.writable RSEGS M 6492024 4 ->
  L5.writable RSEGS M 2147468588 1 -> L5.writable RSEGS M 2147468588 4 -> L5.writable RSEGS M 2147468589 1 -> L5.writable RSEGS M 2147468590 1 ->
  L5.writable RSEGS M 2147468591 1 -> L5.writable RSEGS M 2147468592 4 -> L5.writable RSEGS M 2147468596 1 -> L5.writable RSEGS M 2147468596 4 ->
  L5.writable RSEGS M 2147468597 1 -> L5.writable RSEGS M 2147468598 1 -> L5.writable RSEGS M 2147468599 1 -> L5.writable RSEGS M 2147468600 1 ->
  L5.writable RSEGS M 2147468601 1 -> L5.writable RSEGS M 2147468602 1 -> L5.writable RSEGS M 2147468603 1 -> L5.writable RSEGS M 2147468604 1 ->
  L5.writable RSEGS M 2147468604 4 -> L5.writable RSEGS M 2147468605 1 -> L5.writable RSEGS M 2147468606 1 -> L5.writable RSEGS M 2147468607 1 ->
  L5.writable RSEGS M 2147468608 4 -> L5.writable RSEGS M 2147468612 1 -> L5.writable RSEGS M 2147468612 4 -> L5.writable RSEGS M 2147468613 1 ->
  L5.writable RSEGS M 2147468614 1 -> L5.writable RSEGS M 2147468615 1 -> L5.writable RSEGS M 2147468620 1 -> L5.writable RSEGS M 2147468620 4 ->
  L5.writable RSEGS M 2147468621 1 -> L5.writable RSEGS M 2147468622 1 -> L5.writable RSEGS M 2147468623 1 -> L5.writable RSEGS M 2147468624 4 ->
  L5.writable RSEGS M 2147468628 1 -> L5.writable RSEGS M 2147468628 4 -> L5.writable RSEGS M 2147468629 1 -> L5.writable RSEGS M 2147468630 1 ->
  L5.writable RSEGS M 2147468631 1 -> L5.writable RSEGS M 2147468632 1 -> L5.writable RSEGS M 2147468632 4 -> L5.writable RSEGS M 2147468633 1 ->
  L5.writable RSEGS M 2147468634 1 -> L5.writable RSEGS M 2147468635 1 -> L5.writable RSEGS M 2147468636 4 -> L5.writable RSEGS M 2147468640 1 ->
  L5.writable RSEGS M 2147468640 4 -> L5.writable RSEGS M 2147468641 1 -> L5.writable RSEGS M 2147468642 1 -> L5.writable RSEGS M 2147468643 1 ->
  L5.writable RSEGS M 2147468644 1 -> L5.writable RSEGS M 2147468644 4 -> L5.writable RSEGS M 2147468645 1 -> L5.writable RSEGS M 2147468646 1 ->
  L5.writable RSEGS M 2147468647 1 -> L5.writable RSEGS M 2147468648 4 -> L5.writable RSEGS M 2147468652 1 -> L5.writable RSEGS M 2147468652 4 ->
  L5.writable RSEGS M 2147468653 1 -> L5.writable RSEGS M 2147468654 1 -> L5.writable RSEGS M 2147468655 1 -> L5.writable RSEGS M 2147468656 1 ->
  L5.writable RSEGS M 2147468657 1 -> L5.writable RSEGS M 2147468658 1 -> L5.writable RSEGS M 2147468659 1 -> L5.writable RSEGS M 2147562580 1 ->
  L5.writable RSEGS M 2147562580 4 -> L5.writable RSEGS M 2147562581 1 -> L5.writable RSEGS M 2147562582 1 -> L5.writable RSEGS M 2147562583 1 ->
  L5.writable RSEGS M 2147562584 4 -> L5.writable RSEGS M 2147562588 4 -> L5.writable RSEGS M 2147562592 4 -> L5.writable RSEGS M 2147562596 4 ->
  L5.writable RSEGS M 2147562600 4 -> L5.writable RSEGS M 2147562604 4 -> L5.writable RSEGS M 2147562608 4 -> L5.writable RSEGS M 2147562612 4 ->
  L5.writable RSEGS M 2147562616 4 -> L5.writable RSEGS M 2147562620 4 -> L5.writable RSEGS M 2147562624 4 -> L5.writable RSEGS M 2147562628 4 ->
  L5.writable RSEGS M 2147562632 1 -> L5.writable RSEGS M 2147562632 4 -> L5.writable RSEGS M 2147562633 1 -> L5.writable RSEGS M 2147562634 1 -> L5.writable RSEGS M 2147562635 1 ->
  L5.u32_at RSEGS M 6360160 (V 44%nat) -> 1 <= (V 44%nat) <= 4194303 -> L5.u32_at RSEGS M 6492024 0 -> L5.u8_at RSEGS M 6492059 0 ->
  L5.u64_at RSEGS M 6491496 6491504 -> L5.u32_at RSEGS M 6491488 1 -> L5.u64_at RSEGS M 6491512 775184 -> L5.u64_at RSEGS M 6491768 513096 ->
  L5.u32_at RSEGS M 6491484 0 -> L5.u8_at RSEGS M 1505760 0 -> L5.u64_at RSEGS M 6491504 0 -> L5.u8_at RSEGS M 894160 0 ->
  L5.u64_at RSEGS M 882312 882312 -> L5.u64_at RSEGS M 894080 1 -> L5.u32_at RSEGS M 897872 1 -> L5.u64_at RSEGS M 898032 0 ->
  L5.u8_at RSEGS M 911384 1 -> L5.u64_at RSEGS M 908088 2147450880 -> L5.u64_at RSEGS M 893600 141664 -> L5.u8_at RSEGS M 893616 96 ->
  L5.u8_at RSEGS M 906140 1 -> L5.u64_at RSEGS M 893616 96 -> L5.u64_at RSEGS M 1504992 18446744073709551615 -> L5.u64_at RSEGS M 882712 834348 ->
  L5.u64_at RSEGS M 893656 18446744073709551615 -> L5.u64_at RSEGS M 893664 141760 -> L5.u8_at RSEGS M 893680 32 -> L5.u64_at RSEGS M 893680 32 ->
  L5.u64_at RSEGS M 893720 18446744073709551615 -> L5.u64_at RSEGS M 893728 141792 -> L5.u8_at RSEGS M 893744 96 -> L5.u64_at RSEGS M 893744 96 ->
  L5.u64_at RSEGS M 893784 18446744073709551615 -> L5.u64_at RSEGS M 893792 141920 -> L5.u8_at RSEGS M 893808 96 -> L5.u64_at RSEGS M 893808 96 ->
  L5.u64_at RSEGS M 893848 18446744073709551615 -> L5.u64_at RSEGS M 893856 142016 -> L5.u8_at RSEGS M 893872 96 -> L5.u64_at RSEGS M 893872 96 ->
  L5.u64_at RSEGS M 893912 18446744073709551615 -> L5.u64_at RSEGS M 893920 142112 -> L5.u8_at RSEGS M 893936 96 -> L5.u64_at RSEGS M 893936 96 ->
  L5.u64_at RSEGS M 893976 18446744073709551615 -> L5.u64_at RSEGS M 893984 142208 -> L5.u8_at RSEGS M 894000 32 -> L5.u64_at RSEGS M 894000 32 ->
  L5.u64_at RSEGS M 894040 18446744073709551615 -> L5.u64_at RSEGS M 6493184 0 -> L5.u64_at RSEGS M 893544 893312 -> L5.u32_at RSEGS M 893452 4294967295 ->
  L5.u64_at RSEGS M 893352 0 -> L5.u64_at RSEGS M 893368 0 -> L5.u64_at RSEGS M 893320 0 -> L5.u64_at RSEGS M 893328 0 ->
  L5.u64_at RSEGS M 893304 893072 -> L5.u32_at RSEGS M 893212 4294967295 -> L5.u64_at RSEGS M 893112 0 -> L5.u64_at RSEGS M 893128 0 ->
  L5.u64_at RSEGS M 893080 0 -> L5.u64_at RSEGS M 893088 0 -> L5.u64_at RSEGS M 893064 892832 -> L5.u32_at RSEGS M 892972 4294967295 ->
  L5.u64_at RSEGS M 892872 6493200 -> L5.u64_at RSEGS M 892888 6493200 -> L5.u64_at RSEGS M 892840 0 -> L5.u64_at RSEGS M 892848 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 320) <= bv_unsigned a < ((V 2%nat) - 320) + 320) -> ~ (894080 <= bv_unsigned a < 894080 + 8) -> ~ (894160 <= bv_unsigned a < 894160 + 1) -> ~ (898032 <= bv_unsigned a < 898032 + 8) -> ~ (6491480 <= bv_unsigned a < 6491480 + 1) -> ~ (6491488 <= bv_unsigned a < 6491488 + 4) -> ~ (6491496 <= bv_unsigned a < 6491496 + 8) -> ~ (6492024 <= bv_unsigned a < 6492024 + 4) -> ~ (2147468588 <= bv_unsigned a < 2147468588 + 1) -> ~ (2147468588 <= bv_unsigned a < 2147468588 + 4) -> ~ (2147468589 <= bv_unsigned a < 2147468589 + 1) -> ~ (2147468590 <= bv_unsigned a < 2147468590 + 1) -> ~ (2147468591 <= bv_unsigned a < 2147468591 + 1) -> ~ (2147468592 <= bv_unsigned a < 2147468592 + 4) -> ~ (2147468596 <= bv_unsigned a < 2147468596 + 1) -> ~ (2147468596 <= bv_unsigned a < 2147468596 + 4) -> ~ (2147468597 <= bv_unsigned a < 2147468597 + 1) -> ~ (2147468598 <= bv_unsigned a < 2147468598 + 1) -> ~ (2147468599 <= bv_unsigned a < 2147468599 + 1) -> ~ (2147468600 <= bv_unsigned a < 2147468600 + 1) -> ~ (2147468601 <= bv_unsigned a < 2147468601 + 1) -> ~ (2147468602 <= bv_unsigned a < 2147468602 + 1) -> ~ (2147468603 <= bv_unsigned a < 2147468603 + 1) -> ~ (2147468604 <= bv_unsigned a < 2147468604 + 1) -> ~ (2147468604 <= bv_unsigned a < 2147468604 + 4) -> ~ (2147468605 <= bv_unsigned a < 2147468605 + 1) -> ~ (2147468606 <= bv_unsigned a < 2147468606 + 1) -> ~ (2147468607 <= bv_unsigned a < 2147468607 + 1) -> ~ (2147468608 <= bv_unsigned a < 2147468608 + 4) -> ~ (2147468612 <= bv_unsigned a < 2147468612 + 1) -> ~ (2147468612 <= bv_unsigned a < 2147468612 + 4) -> ~ (2147468613 <= bv_unsigned a < 2147468613 + 1) -> ~ (2147468614 <= bv_unsigned a < 2147468614 + 1) -> ~ (2147468615 <= bv_unsigned a < 2147468615 + 1) -> ~ (2147468620 <= bv_unsigned a < 2147468620 + 1) -> ~ (2147468620 <= bv_unsigned a < 2147468620 + 4) -> ~ (2147468621 <= bv_unsigned a < 2147468621 + 1) -> ~ (2147468622 <= bv_unsigned a < 2147468622 + 1) -> ~ (2147468623 <= bv_unsigned a < 2147468623 + 1) -> ~ (2147468624 <= bv_unsigned a < 2147468624 + 4) -> ~ (2147468628 <= bv_unsigned a < 2147468628 + 1) -> ~ (2147468628 <= bv_unsigned a < 2147468628 + 4) -> ~ (2147468629 <= bv_unsigned a < 2147468629 + 1) -> ~ (2147468630 <= bv_unsigned a < 2147468630 + 1) -> ~ (2147468631 <= bv_unsigned a < 2147468631 + 1) -> ~ (2147468632 <= bv_unsigned a < 2147468632 + 1) -> ~ (2147468632 <= bv_unsigned a < 2147468632 + 4) -> ~ (2147468633 <= bv_unsigned a < 2147468633 + 1) -> ~ (2147468634 <= bv_unsigned a < 2147468634 + 1) -> ~ (2147468635 <= bv_unsigned a < 2147468635 + 1) -> ~ (2147468636 <= bv_unsigned a < 2147468636 + 4) -> ~ (2147468640 <= bv_unsigned a < 2147468640 + 1) -> ~ (2147468640 <= bv_unsigned a < 2147468640 + 4) -> ~ (2147468641 <= bv_unsigned a < 2147468641 + 1) -> ~ (2147468642 <= bv_unsigned a < 2147468642 + 1) -> ~ (2147468643 <= bv_unsigned a < 2147468643 + 1) -> ~ (2147468644 <= bv_unsigned a < 2147468644 + 1) -> ~ (2147468644 <= bv_unsigned a < 2147468644 + 4) -> ~ (2147468645 <= bv_unsigned a < 2147468645 + 1) -> ~ (2147468646 <= bv_unsigned a < 2147468646 + 1) -> ~ (2147468647 <= bv_unsigned a < 2147468647 + 1) -> ~ (2147468648 <= bv_unsigned a < 2147468648 + 4) -> ~ (2147468652 <= bv_unsigned a < 2147468652 + 1) -> ~ (2147468652 <= bv_unsigned a < 2147468652 + 4) -> ~ (2147468653 <= bv_unsigned a < 2147468653 + 1) -> ~ (2147468654 <= bv_unsigned a < 2147468654 + 1) -> ~ (2147468655 <= bv_unsigned a < 2147468655 + 1) -> ~ (2147468656 <= bv_unsigned a < 2147468656 + 1) -> ~ (2147468657 <= bv_unsigned a < 2147468657 + 1) -> ~ (2147468658 <= bv_unsigned a < 2147468658 + 1) -> ~ (2147468659 <= bv_unsigned a < 2147468659 + 1) -> ~ (2147562580 <= bv_unsigned a < 2147562580 + 1) -> ~ (2147562580 <= bv_unsigned a < 2147562580 + 4) -> ~ (2147562581 <= bv_unsigned a < 2147562581 + 1) -> ~ (2147562582 <= bv_unsigned a < 2147562582 + 1) -> ~ (2147562583 <= bv_unsigned a < 2147562583 + 1) -> ~ (2147562584 <= bv_unsigned a < 2147562584 + 4) -> ~ (2147562588 <= bv_unsigned a < 2147562588 + 4) -> ~ (2147562592 <= bv_unsigned a < 2147562592 + 4) -> ~ (2147562596 <= bv_unsigned a < 2147562596 + 4) -> ~ (2147562600 <= bv_unsigned a < 2147562600 + 4) -> ~ (2147562604 <= bv_unsigned a < 2147562604 + 4) -> ~ (2147562608 <= bv_unsigned a < 2147562608 + 4) -> ~ (2147562612 <= bv_unsigned a < 2147562612 + 4) -> ~ (2147562616 <= bv_unsigned a < 2147562616 + 4) -> ~ (2147562620 <= bv_unsigned a < 2147562620 + 4) -> ~ (2147562624 <= bv_unsigned a < 2147562624 + 4) -> ~ (2147562628 <= bv_unsigned a < 2147562628 + 4) -> ~ (2147562632 <= bv_unsigned a < 2147562632 + 1) -> ~ (2147562632 <= bv_unsigned a < 2147562632 + 4) -> ~ (2147562633 <= bv_unsigned a < 2147562633 + 1) -> ~ (2147562634 <= bv_unsigned a < 2147562634 + 1) -> ~ (2147562635 <= bv_unsigned a < 2147562635 + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 320) <= i < ((V 2%nat) - 320) + 320) -> ~ (894080 <= i < 894080 + 8) -> ~ (894160 <= i < 894160 + 1) -> ~ (898032 <= i < 898032 + 8) -> ~ (6491480 <= i < 6491480 + 1) -> ~ (6491488 <= i < 6491488 + 4) -> ~ (6491496 <= i < 6491496 + 8) -> ~ (6492024 <= i < 6492024 + 4) -> ~ (2147468588 <= i < 2147468588 + 1) -> ~ (2147468588 <= i < 2147468588 + 4) -> ~ (2147468589 <= i < 2147468589 + 1) -> ~ (2147468590 <= i < 2147468590 + 1) -> ~ (2147468591 <= i < 2147468591 + 1) -> ~ (2147468592 <= i < 2147468592 + 4) -> ~ (2147468596 <= i < 2147468596 + 1) -> ~ (2147468596 <= i < 2147468596 + 4) -> ~ (2147468597 <= i < 2147468597 + 1) -> ~ (2147468598 <= i < 2147468598 + 1) -> ~ (2147468599 <= i < 2147468599 + 1) -> ~ (2147468600 <= i < 2147468600 + 1) -> ~ (2147468601 <= i < 2147468601 + 1) -> ~ (2147468602 <= i < 2147468602 + 1) -> ~ (2147468603 <= i < 2147468603 + 1) -> ~ (2147468604 <= i < 2147468604 + 1) -> ~ (2147468604 <= i < 2147468604 + 4) -> ~ (2147468605 <= i < 2147468605 + 1) -> ~ (2147468606 <= i < 2147468606 + 1) -> ~ (2147468607 <= i < 2147468607 + 1) -> ~ (2147468608 <= i < 2147468608 + 4) -> ~ (2147468612 <= i < 2147468612 + 1) -> ~ (2147468612 <= i < 2147468612 + 4) -> ~ (2147468613 <= i < 2147468613 + 1) -> ~ (2147468614 <= i < 2147468614 + 1) -> ~ (2147468615 <= i < 2147468615 + 1) -> ~ (2147468620 <= i < 2147468620 + 1) -> ~ (2147468620 <= i < 2147468620 + 4) -> ~ (2147468621 <= i < 2147468621 + 1) -> ~ (2147468622 <= i < 2147468622 + 1) -> ~ (2147468623 <= i < 2147468623 + 1) -> ~ (2147468624 <= i < 2147468624 + 4) -> ~ (2147468628 <= i < 2147468628 + 1) -> ~ (2147468628 <= i < 2147468628 + 4) -> ~ (2147468629 <= i < 2147468629 + 1) -> ~ (2147468630 <= i < 2147468630 + 1) -> ~ (2147468631 <= i < 2147468631 + 1) -> ~ (2147468632 <= i < 2147468632 + 1) -> ~ (2147468632 <= i < 2147468632 + 4) -> ~ (2147468633 <= i < 2147468633 + 1) -> ~ (2147468634 <= i < 2147468634 + 1) -> ~ (2147468635 <= i < 2147468635 + 1) -> ~ (2147468636 <= i < 2147468636 + 4) -> ~ (2147468640 <= i < 2147468640 + 1) -> ~ (2147468640 <= i < 2147468640 + 4) -> ~ (2147468641 <= i < 2147468641 + 1) -> ~ (2147468642 <= i < 2147468642 + 1) -> ~ (2147468643 <= i < 2147468643 + 1) -> ~ (2147468644 <= i < 2147468644 + 1) -> ~ (2147468644 <= i < 2147468644 + 4) -> ~ (2147468645 <= i < 2147468645 + 1) -> ~ (2147468646 <= i < 2147468646 + 1) -> ~ (2147468647 <= i < 2147468647 + 1) -> ~ (2147468648 <= i < 2147468648 + 4) -> ~ (2147468652 <= i < 2147468652 + 1) -> ~ (2147468652 <= i < 2147468652 + 4) -> ~ (2147468653 <= i < 2147468653 + 1) -> ~ (2147468654 <= i < 2147468654 + 1) -> ~ (2147468655 <= i < 2147468655 + 1) -> ~ (2147468656 <= i < 2147468656 + 1) -> ~ (2147468657 <= i < 2147468657 + 1) -> ~ (2147468658 <= i < 2147468658 + 1) -> ~ (2147468659 <= i < 2147468659 + 1) -> ~ (2147562580 <= i < 2147562580 + 1) -> ~ (2147562580 <= i < 2147562580 + 4) -> ~ (2147562581 <= i < 2147562581 + 1) -> ~ (2147562582 <= i < 2147562582 + 1) -> ~ (2147562583 <= i < 2147562583 + 1) -> ~ (2147562584 <= i < 2147562584 + 4) -> ~ (2147562588 <= i < 2147562588 + 4) -> ~ (2147562592 <= i < 2147562592 + 4) -> ~ (2147562596 <= i < 2147562596 + 4) -> ~ (2147562600 <= i < 2147562600 + 4) -> ~ (2147562604 <= i < 2147562604 + 4) -> ~ (2147562608 <= i < 2147562608 + 4) -> ~ (2147562612 <= i < 2147562612 + 4) -> ~ (2147562616 <= i < 2147562616 + 4) -> ~ (2147562620 <= i < 2147562620 + 4) -> ~ (2147562624 <= i < 2147562624 + 4) -> ~ (2147562628 <= i < 2147562628 + 4) -> ~ (2147562632 <= i < 2147562632 + 1) -> ~ (2147562632 <= i < 2147562632 + 4) -> ~ (2147562633 <= i < 2147562633 + 1) -> ~ (2147562634 <= i < 2147562634 + 1) -> ~ (2147562635 <= i < 2147562635 + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xbd464 M) (st fx' R' 0xbd23c M')
        /\ (forall x, In x KS_dpXm -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 775384
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 16)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 6) = Z_to_bv 64 1152921504606846976
        /\ getr R' (reg 7) = Z_to_bv 64 0
        /\ getr R' (reg 8) = getr R (reg 10)
        /\ getr R' (reg 11) = getr R (reg 10)
        /\ getr R' (reg 12) = Z_to_bv 64 6917529027641081856
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 17293822569102704639
        /\ getr R' (reg 15) = Z_to_bv 64 1152920405095219200
        /\ getr R' (reg 16) = Z_to_bv 64 18446742974197923840
        /\ getr R' (reg 17) = Z_to_bv 64 94
        /\ getr R' (reg 28) = Z_to_bv 64 897968
        /\ L5.u64_at RSEGS M' 894080 0
        /\ L5.u64_at RSEGS M' 898032 0
        /\ L5.u32_at RSEGS M' 2147562620 0
        /\ L5.u32_at RSEGS M' 2147562616 0
        /\ L5.u32_at RSEGS M' 2147562612 0
        /\ L5.u32_at RSEGS M' 2147562608 0
        /\ L5.u32_at RSEGS M' 2147562604 0
        /\ L5.u32_at RSEGS M' 2147562600 0
        /\ L5.u32_at RSEGS M' 2147562596 0
        /\ L5.u32_at RSEGS M' 2147562592 0
        /\ L5.u32_at RSEGS M' 2147562628 0
        /\ L5.u32_at RSEGS M' 2147562624 0
        /\ L5.u32_at RSEGS M' 2147562588 0
        /\ L5.u32_at RSEGS M' 2147562584 0
        /\ L5.u32_at RSEGS M' 2147562632 0
        /\ L5.u32_at RSEGS M' 2147562580 0
        /\ L5.u8_at RSEGS M' 2147468658 0
        /\ L5.u8_at RSEGS M' 2147468657 0
        /\ L5.u8_at RSEGS M' 2147468659 0
        /\ L5.u8_at RSEGS M' 2147468656 0
        /\ L5.u32_at RSEGS M' 2147468648 0
        /\ L5.u32_at RSEGS M' 2147468644 0
        /\ L5.u32_at RSEGS M' 2147468652 0
        /\ L5.u32_at RSEGS M' 2147468636 0
        /\ L5.u32_at RSEGS M' 2147468632 0
        /\ L5.u32_at RSEGS M' 2147468640 0
        /\ L5.u32_at RSEGS M' 2147468624 0
        /\ L5.u32_at RSEGS M' 2147468620 0
        /\ L5.u32_at RSEGS M' 2147468628 0
        /\ L5.u32_at RSEGS M' 2147468608 0
        /\ L5.u32_at RSEGS M' 2147468604 0
        /\ L5.u32_at RSEGS M' 2147468612 0
        /\ L5.u8_at RSEGS M' 2147468602 0
        /\ L5.u8_at RSEGS M' 2147468601 0
        /\ L5.u8_at RSEGS M' 2147468603 0
        /\ L5.u8_at RSEGS M' 2147468600 0
        /\ L5.u32_at RSEGS M' 2147468592 0
        /\ L5.u32_at RSEGS M' 2147468588 0
        /\ L5.u32_at RSEGS M' 2147468596 0
        /\ L5.u8_at RSEGS M' 894160 1
        /\ L5.u8_at RSEGS M' 6491480 1
        /\ L5.u64_at RSEGS M' 6491496 0
        /\ L5.u32_at RSEGS M' 6491488 32
        /\ L5.u32_at RSEGS M' 6492024 (V 44%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros [HV2l HV2r] [HV44l HV44r] G2 G4 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57 K58 K59 K60 K61 K62 K63 K64 K65 K66 K67 K68 K69 K70 K71 K72 K73 K74 K75 K76 K77 K78 K79 K80 K81 K82 K83 K84 K85 K86 K87 K88 K89 K90 K91 K92 K93 K94 K95 K96 K97 [K98l K98r] K99 K100 K101 K102 K103 K104 K105 K106 K107 K108 K109 K110 K111 K112 K113 K114 K115 K116 K117 K118 K119 K120 K121 K122 K123 K124 K125 K126 K127 K128 K129 K130 K131 K132 K133 K134 K135 K136 K137 K138 K139 K140 K141 K142 K143 K144 K145 K146 K147 K148 K149 K150 K151 K152 K153 K154 K155 K156 K157 K158 K159 K160 K161 K162 K163 K164.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 44%nat => (V 44%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 45%nat. }
  assert (HR: regs_ok E PdpXm.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PdpXm.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PdpXm.kn0).
  { unfold know_ok, PdpXm.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K50]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K55]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K57]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K58]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K60]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K61]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K62]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K63]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K64]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K65]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K66]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K67]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K68]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K69]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K70]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K71]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K72]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K73]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K74]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K75]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K76]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K77]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K78]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K79]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K80]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K81]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K82]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K83]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K84]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K85]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K86]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K87]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K88]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K89]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K90]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K91]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K92]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K93]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K94]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K95]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K96]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV44l HV44r K98l K98r) | clear; lia | clear; lia | exactA K97]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV44l HV44r K98l K98r) | exact (conj K98l K98r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K99]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K100]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K101]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K102]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K103]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K104]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K105]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K106]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K107]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K108]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K109]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K110]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K111]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K112]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K113]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K114]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K115]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K116]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K117]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K118]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K119]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K120]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K121]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K122]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K123]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K124]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K125]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K126]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K127]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K128]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K129]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K130]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K131]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K132]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K133]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K134]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K135]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K136]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K137]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K138]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K139]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K140]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K141]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K142]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K143]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K144]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K145]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K146]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K147]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K148]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K149]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K150]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K151]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K152]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K153]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K154]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K155]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K156]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K157]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K158]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K159]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K160]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K161]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K162]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K163]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K164]. }
    apply Forall_nil. }
  destruct (PdpXm.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PdpXm.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 320) <= bv_unsigned a < ((V 2%nat) - 320) + 320) -> ~ (894080 <= bv_unsigned a < 894080 + 8) -> ~ (894160 <= bv_unsigned a < 894160 + 1) -> ~ (898032 <= bv_unsigned a < 898032 + 8) -> ~ (6491480 <= bv_unsigned a < 6491480 + 1) -> ~ (6491488 <= bv_unsigned a < 6491488 + 4) -> ~ (6491496 <= bv_unsigned a < 6491496 + 8) -> ~ (6492024 <= bv_unsigned a < 6492024 + 4) -> ~ (2147468588 <= bv_unsigned a < 2147468588 + 1) -> ~ (2147468588 <= bv_unsigned a < 2147468588 + 4) -> ~ (2147468589 <= bv_unsigned a < 2147468589 + 1) -> ~ (2147468590 <= bv_unsigned a < 2147468590 + 1) -> ~ (2147468591 <= bv_unsigned a < 2147468591 + 1) -> ~ (2147468592 <= bv_unsigned a < 2147468592 + 4) -> ~ (2147468596 <= bv_unsigned a < 2147468596 + 1) -> ~ (2147468596 <= bv_unsigned a < 2147468596 + 4) -> ~ (2147468597 <= bv_unsigned a < 2147468597 + 1) -> ~ (2147468598 <= bv_unsigned a < 2147468598 + 1) -> ~ (2147468599 <= bv_unsigned a < 2147468599 + 1) -> ~ (2147468600 <= bv_unsigned a < 2147468600 + 1) -> ~ (2147468601 <= bv_unsigned a < 2147468601 + 1) -> ~ (2147468602 <= bv_unsigned a < 2147468602 + 1) -> ~ (2147468603 <= bv_unsigned a < 2147468603 + 1) -> ~ (2147468604 <= bv_unsigned a < 2147468604 + 1) -> ~ (2147468604 <= bv_unsigned a < 2147468604 + 4) -> ~ (2147468605 <= bv_unsigned a < 2147468605 + 1) -> ~ (2147468606 <= bv_unsigned a < 2147468606 + 1) -> ~ (2147468607 <= bv_unsigned a < 2147468607 + 1) -> ~ (2147468608 <= bv_unsigned a < 2147468608 + 4) -> ~ (2147468612 <= bv_unsigned a < 2147468612 + 1) -> ~ (2147468612 <= bv_unsigned a < 2147468612 + 4) -> ~ (2147468613 <= bv_unsigned a < 2147468613 + 1) -> ~ (2147468614 <= bv_unsigned a < 2147468614 + 1) -> ~ (2147468615 <= bv_unsigned a < 2147468615 + 1) -> ~ (2147468620 <= bv_unsigned a < 2147468620 + 1) -> ~ (2147468620 <= bv_unsigned a < 2147468620 + 4) -> ~ (2147468621 <= bv_unsigned a < 2147468621 + 1) -> ~ (2147468622 <= bv_unsigned a < 2147468622 + 1) -> ~ (2147468623 <= bv_unsigned a < 2147468623 + 1) -> ~ (2147468624 <= bv_unsigned a < 2147468624 + 4) -> ~ (2147468628 <= bv_unsigned a < 2147468628 + 1) -> ~ (2147468628 <= bv_unsigned a < 2147468628 + 4) -> ~ (2147468629 <= bv_unsigned a < 2147468629 + 1) -> ~ (2147468630 <= bv_unsigned a < 2147468630 + 1) -> ~ (2147468631 <= bv_unsigned a < 2147468631 + 1) -> ~ (2147468632 <= bv_unsigned a < 2147468632 + 1) -> ~ (2147468632 <= bv_unsigned a < 2147468632 + 4) -> ~ (2147468633 <= bv_unsigned a < 2147468633 + 1) -> ~ (2147468634 <= bv_unsigned a < 2147468634 + 1) -> ~ (2147468635 <= bv_unsigned a < 2147468635 + 1) -> ~ (2147468636 <= bv_unsigned a < 2147468636 + 4) -> ~ (2147468640 <= bv_unsigned a < 2147468640 + 1) -> ~ (2147468640 <= bv_unsigned a < 2147468640 + 4) -> ~ (2147468641 <= bv_unsigned a < 2147468641 + 1) -> ~ (2147468642 <= bv_unsigned a < 2147468642 + 1) -> ~ (2147468643 <= bv_unsigned a < 2147468643 + 1) -> ~ (2147468644 <= bv_unsigned a < 2147468644 + 1) -> ~ (2147468644 <= bv_unsigned a < 2147468644 + 4) -> ~ (2147468645 <= bv_unsigned a < 2147468645 + 1) -> ~ (2147468646 <= bv_unsigned a < 2147468646 + 1) -> ~ (2147468647 <= bv_unsigned a < 2147468647 + 1) -> ~ (2147468648 <= bv_unsigned a < 2147468648 + 4) -> ~ (2147468652 <= bv_unsigned a < 2147468652 + 1) -> ~ (2147468652 <= bv_unsigned a < 2147468652 + 4) -> ~ (2147468653 <= bv_unsigned a < 2147468653 + 1) -> ~ (2147468654 <= bv_unsigned a < 2147468654 + 1) -> ~ (2147468655 <= bv_unsigned a < 2147468655 + 1) -> ~ (2147468656 <= bv_unsigned a < 2147468656 + 1) -> ~ (2147468657 <= bv_unsigned a < 2147468657 + 1) -> ~ (2147468658 <= bv_unsigned a < 2147468658 + 1) -> ~ (2147468659 <= bv_unsigned a < 2147468659 + 1) -> ~ (2147562580 <= bv_unsigned a < 2147562580 + 1) -> ~ (2147562580 <= bv_unsigned a < 2147562580 + 4) -> ~ (2147562581 <= bv_unsigned a < 2147562581 + 1) -> ~ (2147562582 <= bv_unsigned a < 2147562582 + 1) -> ~ (2147562583 <= bv_unsigned a < 2147562583 + 1) -> ~ (2147562584 <= bv_unsigned a < 2147562584 + 4) -> ~ (2147562588 <= bv_unsigned a < 2147562588 + 4) -> ~ (2147562592 <= bv_unsigned a < 2147562592 + 4) -> ~ (2147562596 <= bv_unsigned a < 2147562596 + 4) -> ~ (2147562600 <= bv_unsigned a < 2147562600 + 4) -> ~ (2147562604 <= bv_unsigned a < 2147562604 + 4) -> ~ (2147562608 <= bv_unsigned a < 2147562608 + 4) -> ~ (2147562612 <= bv_unsigned a < 2147562612 + 4) -> ~ (2147562616 <= bv_unsigned a < 2147562616 + 4) -> ~ (2147562620 <= bv_unsigned a < 2147562620 + 4) -> ~ (2147562624 <= bv_unsigned a < 2147562624 + 4) -> ~ (2147562628 <= bv_unsigned a < 2147562628 + 4) -> ~ (2147562632 <= bv_unsigned a < 2147562632 + 1) -> ~ (2147562632 <= bv_unsigned a < 2147562632 + 4) -> ~ (2147562633 <= bv_unsigned a < 2147562633 + 1) -> ~ (2147562634 <= bv_unsigned a < 2147562634 + 1) -> ~ (2147562635 <= bv_unsigned a < 2147562635 + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8 Hn9 Hn10 Hn11 Hn12 Hn13 Hn14 Hn15 Hn16 Hn17 Hn18 Hn19 Hn20 Hn21 Hn22 Hn23 Hn24 Hn25 Hn26 Hn27 Hn28 Hn29 Hn30 Hn31 Hn32 Hn33 Hn34 Hn35 Hn36 Hn37 Hn38 Hn39 Hn40 Hn41 Hn42 Hn43 Hn44 Hn45 Hn46 Hn47 Hn48 Hn49 Hn50 Hn51 Hn52 Hn53 Hn54 Hn55 Hn56 Hn57 Hn58 Hn59 Hn60 Hn61 Hn62 Hn63 Hn64 Hn65 Hn66 Hn67 Hn68 Hn69 Hn70 Hn71 Hn72 Hn73 Hn74 Hn75 Hn76 Hn77 Hn78 Hn79 Hn80 Hn81 Hn82 Hn83 Hn84 Hn85 Hn86 Hn87 Hn88 Hn89 Hn90 Hn91 Hn92. apply Hfr. unfold PdpXm.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn6; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn7; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn8; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn9; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn10; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn11; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn12; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn13; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn14; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn15; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn16; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn17; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn18; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn19; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn20; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn21; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn22; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn23; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn24; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn25; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn26; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn27; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn28; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn29; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn30; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn31; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn32; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn33; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn34; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn35; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn36; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn37; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn38; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn39; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn40; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn41; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn42; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn43; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn44; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn45; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn46; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn47; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn48; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn49; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn50; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn51; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn52; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn53; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn54; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn55; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn56; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn57; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn58; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn59; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn60; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn61; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn62; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn63; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn64; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn65; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn66; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn67; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn68; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn69; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn70; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn71; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn72; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn73; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn74; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn75; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn76; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn77; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn78; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn79; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn80; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn81; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn82; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn83; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn84; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn85; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn86; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn87; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn88; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn89; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn90; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn91; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn92; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8 Hn9 Hn10 Hn11 Hn12 Hn13 Hn14 Hn15 Hn16 Hn17 Hn18 Hn19 Hn20 Hn21 Hn22 Hn23 Hn24 Hn25 Hn26 Hn27 Hn28 Hn29 Hn30 Hn31 Hn32 Hn33 Hn34 Hn35 Hn36 Hn37 Hn38 Hn39 Hn40 Hn41 Hn42 Hn43 Hn44 Hn45 Hn46 Hn47 Hn48 Hn49 Hn50 Hn51 Hn52 Hn53 Hn54 Hn55 Hn56 Hn57 Hn58 Hn59 Hn60 Hn61 Hn62 Hn63 Hn64 Hn65 Hn66 Hn67 Hn68 Hn69 Hn70 Hn71 Hn72 Hn73 Hn74 Hn75 Hn76 Hn77 Hn78 Hn79 Hn80 Hn81 Hn82 Hn83 Hn84 Hn85 Hn86 Hn87 Hn88 Hn89 Hn90 Hn91 Hn92. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PdpXm.ps0) with 0xbd23c in Hms. change (SR.ps_regs PdpXm.ps0) with (map (fun i => (i, nth i PdpXm.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PdpXm.ps0) with PdpXm.cells0 in Hcells. unfold PdpXm.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PdpXm.regs0 PdpXm.regs_out0 56 KS_dpXm KS_dpXm_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PdpXm.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PdpXm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdpXm.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PdpXm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdpXm.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PdpXm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdpXm.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PdpXm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdpXm.regs_out0 E' R' 7 Hregs) by (clear; lia). cbn [nth PdpXm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdpXm.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PdpXm.regs_out0]. rewrite (BG.edenot_kept 56 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PdpXm.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PdpXm.regs_out0]. rewrite (BG.edenot_kept 56 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PdpXm.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PdpXm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdpXm.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PdpXm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdpXm.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PdpXm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdpXm.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PdpXm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdpXm.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PdpXm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdpXm.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PdpXm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PdpXm.regs_out0 E' R' 28 Hregs) by (clear; lia). cbn [nth PdpXm.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 36%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 37%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 38%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 39%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 40%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 41%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 42%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 43%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV44l HV44r K98l K98r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 44%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 45%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End AS0DRVP_dpXm.
