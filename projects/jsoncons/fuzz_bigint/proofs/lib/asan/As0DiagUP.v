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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegZ_duA LibSegZ_duB LibSegZ_duD LibSegZ_duDs LibSegZ_duDl LibSegZ_duEa LibSegZ_duEb LibSegZ_duFa LibSegZ_duGa LibSegZ_duGb1 LibSegZ_duGb2 LibSegZ_duEc LibSegZ_duGc.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module AS0DIAGUP.
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
Module PduA := LibSegZ_duA.
Definition KS_duA : list nat := Eval vm_compute in (BG.kept_list 140 PduA.regs0 PduA.regs_out0).
Lemma KS_duA_ok : BG.kept_ok 140 PduA.regs0 PduA.regs_out0 KS_duA = true. Proof. vm_compute. reflexivity. Qed.
Lemma duA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 580508 -> getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 892832 -> getr R (reg 11) = Z_to_bv 64 89955 -> getr R (reg 12) = Z_to_bv 64 (V 33%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 2352) 2352 -> L5.defined M ((V 2%nat) - 2352) 2352 ->
  L5.img_clear M 65536 880640 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 131071 -> (((V 2%nat) - 2352) + 2352 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 2352)) ->
  L5.u64_at RSEGS M 2147462120 0 -> L5.u8_at RSEGS M 911384 1 -> L5.u8_at RSEGS M 1504956 1 -> L5.u64_at RSEGS M 908088 2147450880 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 2352) <= bv_unsigned a < ((V 2%nat) - 2352) + 2352) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 2352) <= i < ((V 2%nat) - 2352) + 2352) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x4dbec M) (st fx' R' 0x50a78 M')
        /\ (forall x, In x KS_duA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 330096
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 2352)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 9) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 115
        /\ getr R' (reg 13) = Z_to_bv 64 115
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 10
        /\ getr R' (reg 19) = Z_to_bv 64 89964
        /\ getr R' (reg 20) = Z_to_bv 64 88496
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 2%nat) - 40)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 9
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 2%nat) - 2296)
        /\ getr R' (reg 25) = Z_to_bv 64 12297829382473034410
        /\ getr R' (reg 26) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 27) = Z_to_bv 64 37
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2292) 115
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2304) 89964
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2296) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2312) 89962
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2320) 18446744073709551615
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2289) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2290) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2291) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2293) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2294) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2295) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2321) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2322) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2323) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2324) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2325) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2326) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2327) 0
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 2328) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2344) ((V 2%nat) - 232)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 2336) 131724
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 216) (bv_unsigned (getr R (reg 27)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 208) (bv_unsigned (getr R (reg 26)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 200) (bv_unsigned (getr R (reg 25)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 192) (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 184) (bv_unsigned (getr R (reg 23)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 176) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 168) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 152) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 144) ((V 2%nat) - 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 892832
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 89955
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) 332900
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 96) ((V 2%nat) - 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 88) ((V 2%nat) - 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) ((V 2%nat) - 48)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 15)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 14)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 13)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 17)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 16)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 80) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 580508
        /\ L5.defined M' ((V 2%nat) - 2352) 8
        /\ L5.defined M' ((V 2%nat) - 2288) 2072
        /\ L5.defined M' ((V 2%nat) - 112) 8).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] G1 G2 G10 G11 G12 [K0l K0r] K1 K2 K3 K4 [K5l K5r] [K6l K6r] K7 K8 K9 K10 K11.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PduA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduA.kn0).
  { unfold know_ok, PduA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K11]. }
    apply Forall_nil. }
  destruct (PduA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PduA.NX0 with 140%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 2352) <= bv_unsigned a < ((V 2%nat) - 2352) + 2352) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PduA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduA.ps0) with 0x50a78 in Hms. change (SR.ps_regs PduA.ps0) with (map (fun i => (i, nth i PduA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduA.ps0) with PduA.cells0 in Hcells. unfold PduA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduA.regs0 PduA.regs_out0 140 KS_duA KS_duA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduA.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PduA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 36%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 37%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 38%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 39%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 40%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 41%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 42%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 43%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 44%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 45%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 46%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 47%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 48%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 49%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduB := LibSegZ_duB.
Definition KS_duB : list nat := Eval vm_compute in (BG.kept_list 140 PduB.regs0 PduB.regs_out0).
Lemma KS_duB_ok : BG.kept_ok 140 PduB.regs0 PduB.regs_out0 KS_duB = true. Proof. vm_compute. reflexivity. Qed.
Lemma duB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 20%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 23%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 25%nat) < 2 ^ 64 -> 0 <= (V 26%nat) < 2 ^ 64 -> 0 <= (V 27%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 120%nat) < 2 ^ 64 -> 0 <= (V 121%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 -> 0 <= (V 123%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 ((V 2%nat) + 2240) -> getr R (reg 19) = Z_to_bv 64 89964 -> getr R (reg 20) = Z_to_bv 64 (V 120%nat) -> getr R (reg 21) = Z_to_bv 64 (V 121%nat) -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) -> getr R (reg 23) = Z_to_bv 64 (V 123%nat) -> getr R (reg 24) = Z_to_bv 64 ((V 2%nat) + 56) -> getr R (reg 25) = Z_to_bv 64 12297829382473034410 -> getr R (reg 26) = Z_to_bv 64 18446744073709551615 -> getr R (reg 27) = Z_to_bv 64 37 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 896) 3136 -> L5.defined M ((V 2%nat) - 896) 3136 ->
  L5.img_clear M 65536 880640 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 131071 -> (((V 2%nat) - 896) + 3136 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 896)) ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147451102) 24 -> L5.u64_at RSEGS M 2147462120 0 -> L5.writable RSEGS M 892832 4 -> L5.writable RSEGS M 892840 8 ->
  L5.writable RSEGS M 892848 8 -> L5.writable RSEGS M 892864 8 -> L5.writable RSEGS M 892872 8 -> L5.writable RSEGS M 892888 8 ->
  L5.writable RSEGS M 892920 8 -> L5.writable RSEGS M 892928 8 -> L5.writable RSEGS M 892968 4 -> L5.u64_at RSEGS M ((V 2%nat) + 2232) 332900 ->
  L5.u64_at RSEGS M ((V 2%nat) + 2224) 89955 -> L5.u64_at RSEGS M ((V 2%nat) + 2216) 892832 -> L5.u64_at RSEGS M ((V 2%nat) + 2208) ((V 2%nat) + 2304) -> L5.u64_at RSEGS M ((V 2%nat) + 2200) (V 19%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 2192) (V 20%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2184) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2176) (V 22%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2168) (V 23%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 2160) (V 24%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2152) (V 25%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2144) (V 26%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 2136) (V 27%nat) ->
  L5.u64_at RSEGS M 882416 801848 -> L5.u64_at RSEGS M ((V 2%nat) + 2264) ((V 2%nat) + 2304) -> L5.u64_at RSEGS M 6491464 (V 40%nat) -> L5.u32_at RSEGS M 892972 4294967295 ->
  L5.u32_at RSEGS M 892832 5 -> L5.u64_at RSEGS M 892928 0 -> L5.u64_at RSEGS M 892920 6493200 -> L5.u32_at RSEGS M 892968 0 ->
  L5.u32_at RSEGS M 892976 4294967295 -> L5.u8_at RSEGS M 911385 1 -> L5.u64_at RSEGS M 908088 2147450880 -> L5.u64_at RSEGS M 882704 833320 ->
  L5.u64_at RSEGS M ((V 2%nat) + 2304) (V 33%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 896) <= bv_unsigned a < ((V 2%nat) - 896) + 3136) -> ~ (892832 <= bv_unsigned a < 892832 + 4) -> ~ (892840 <= bv_unsigned a < 892840 + 8) -> ~ (892848 <= bv_unsigned a < 892848 + 8) -> ~ (892864 <= bv_unsigned a < 892864 + 8) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> ~ (892888 <= bv_unsigned a < 892888 + 8) -> ~ (892920 <= bv_unsigned a < 892920 + 8) -> ~ (892928 <= bv_unsigned a < 892928 + 8) -> ~ (892968 <= bv_unsigned a < 892968 + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 896) <= i < ((V 2%nat) - 896) + 3136) -> ~ (892832 <= i < 892832 + 4) -> ~ (892840 <= i < 892840 + 8) -> ~ (892848 <= i < 892848 + 8) -> ~ (892864 <= i < 892864 + 8) -> ~ (892872 <= i < 892872 + 8) -> ~ (892888 <= i < 892888 + 8) -> ~ (892920 <= i < 892920 + 8) -> ~ (892928 <= i < 892928 + 8) -> ~ (892968 <= i < 892968 + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x509dc M) (st fx' R' 0x4dbb4 M')
        /\ (forall x, In x KS_duB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 803840
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 1328)
        /\ getr R' (reg 5) = Z_to_bv 64 0
        /\ getr R' (reg 8) = Z_to_bv 64 37
        /\ getr R' (reg 9) = Z_to_bv 64 2147483647
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 2147483647
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 2%nat) + 1872)
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) + 2312)
        /\ getr R' (reg 14) = Z_to_bv 64 31
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551558
        /\ getr R' (reg 16) = Z_to_bv 64 115
        /\ getr R' (reg 17) = Z_to_bv 64 8
        /\ getr R' (reg 18) = Z_to_bv 64 2147483640
        /\ getr R' (reg 19) = Z_to_bv 64 7
        /\ getr R' (reg 20) = Z_to_bv 64 892832
        /\ getr R' (reg 21) = Z_to_bv 64 89964
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 26) = Z_to_bv 64 0
        /\ getr R' (reg 27) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1440) (V 33%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1872) ((V 2%nat) + 2312)
        /\ L5.u64_at RSEGS M' 892872 ((V 2%nat) + 1895)
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1894) 32
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1893) 58
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1892) 101
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1891) 103
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1890) 97
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1889) 115
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 1888) 117
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1368) 18446744072850558157
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1376) 18446744073709486079
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1432) 214748364
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1408) 75913
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1760) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1424) 6491464
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1416) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1400) ((V 2%nat) + 1872)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1384) ((V 2%nat) + 1968)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1392) ((V 2%nat) + 2136)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1768) (V 27%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1776) (V 26%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1784) (V 25%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1792) (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1800) (V 23%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1808) (V 22%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1816) 5
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1824) 6493200
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1832) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1840) 6491464
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1848) 89955
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1856) 892832
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1864) 802112
        /\ L5.u64_at RSEGS M' 892864 ((V 2%nat) + 1968)
        /\ L5.u64_at RSEGS M' 892848 0
        /\ L5.u64_at RSEGS M' 892840 0
        /\ L5.u64_at RSEGS M' 892888 ((V 2%nat) + 1888)
        /\ L5.u32_at RSEGS M' 892968 18446744073709551615
        /\ L5.u64_at RSEGS M' 892928 80
        /\ L5.u64_at RSEGS M' 892920 ((V 2%nat) + 1888)
        /\ L5.u32_at RSEGS M' 892832 5
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2160) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2152) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2144) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2136) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2168) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 1880) ((V 2%nat) + 2304)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2176) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2184) (V 21%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2192) (V 20%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2200) (V 19%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2208) ((V 2%nat) + 2304)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2216) 892832
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2224) 89955
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 2232) 332964
        /\ L5.defined M' ((V 2%nat) + 1328) 40
        /\ L5.defined M' ((V 2%nat) + 1448) 312
        /\ L5.defined M' ((V 2%nat) + 1895) 241).
Proof.
  intros [HV2l HV2r] [HV19l HV19r] [HV20l HV20r] [HV21l HV21r] [HV22l HV22r] [HV23l HV23r] [HV24l HV24r] [HV25l HV25r] [HV26l HV26r] [HV27l HV27r] [HV33l HV33r] [HV34l HV34r] [HV40l HV40r] [HV120l HV120r] [HV121l HV121r] [HV122l HV122r] [HV123l HV123r] G2 G8 G19 G20 G21 G22 G23 G24 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 [K5l K5r] [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 19%nat => Z_to_bv 64 (V 19%nat) | 20%nat => Z_to_bv 64 (V 20%nat) | 21%nat => Z_to_bv 64 (V 21%nat) | 22%nat => Z_to_bv 64 (V 22%nat) | 23%nat => Z_to_bv 64 (V 23%nat) | 24%nat => Z_to_bv 64 (V 24%nat) | 25%nat => Z_to_bv 64 (V 25%nat) | 26%nat => Z_to_bv 64 (V 26%nat) | 27%nat => Z_to_bv 64 (V 27%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 120%nat => Z_to_bv 64 (V 120%nat) | 121%nat => Z_to_bv 64 (V 121%nat) | 122%nat => Z_to_bv 64 (V 122%nat) | 123%nat => Z_to_bv 64 (V 123%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 19%nat => (V 19%nat) | 20%nat => (V 20%nat) | 21%nat => (V 21%nat) | 22%nat => (V 22%nat) | 23%nat => (V 23%nat) | 24%nat => (V 24%nat) | 25%nat => (V 25%nat) | 26%nat => (V 26%nat) | 27%nat => (V 27%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 40%nat => (V 40%nat) | 120%nat => (V 120%nat) | 121%nat => (V 121%nat) | 122%nat => (V 122%nat) | 123%nat => (V 123%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 124%nat. }
  assert (HR: regs_ok E PduB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduB.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduB.kn0).
  { unfold know_ok, PduB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV20l HV20r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV22l HV22r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV23l HV23r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV25l HV25r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV26l HV26r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV27l HV27r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K44]. }
    apply Forall_nil. }
  destruct (PduB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PduB.NX0 with 140%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 896) <= bv_unsigned a < ((V 2%nat) - 896) + 3136) -> ~ (892832 <= bv_unsigned a < 892832 + 4) -> ~ (892840 <= bv_unsigned a < 892840 + 8) -> ~ (892848 <= bv_unsigned a < 892848 + 8) -> ~ (892864 <= bv_unsigned a < 892864 + 8) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> ~ (892888 <= bv_unsigned a < 892888 + 8) -> ~ (892920 <= bv_unsigned a < 892920 + 8) -> ~ (892928 <= bv_unsigned a < 892928 + 8) -> ~ (892968 <= bv_unsigned a < 892968 + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8 Hn9. apply Hfr. unfold PduB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn6; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn7; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn8; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn9; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8 Hn9. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduB.ps0) with 0x4dbb4 in Hms. change (SR.ps_regs PduB.ps0) with (map (fun i => (i, nth i PduB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduB.ps0) with PduB.cells0 in Hcells. unfold PduB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduB.regs0 PduB.regs_out0 140 KS_duB KS_duB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduB.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PduB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K5l K5r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV27l HV27r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV26l HV26r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV25l HV25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV24l HV24r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV23l HV23r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 25%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV22l HV22r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 26%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 27%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 28%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 29%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 30%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 31%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 32%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 33%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 34%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 35%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 36%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 37%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 38%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 39%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 40%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 41%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 42%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 43%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 44%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 45%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 46%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 47%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 48%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV21l HV21r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 49%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV20l HV20r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 50%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV19l HV19r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 51%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 52%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 53%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 54%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 55%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 56%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 57%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduD := LibSegZ_duD.
Definition KS_duD : list nat := Eval vm_compute in (BG.kept_list 140 PduD.regs0 PduD.regs_out0).
Lemma KS_duD_ok : BG.kept_ok 140 PduD.regs0 PduD.regs_out0 KS_duD = true. Proof. vm_compute. reflexivity. Qed.
Lemma duD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 37 -> getr R (reg 9) = Z_to_bv 64 2147483647 -> getr R (reg 10) = Z_to_bv 64 (V 34%nat) -> getr R (reg 18) = Z_to_bv 64 2147483640 -> getr R (reg 19) = Z_to_bv 64 7 -> getr R (reg 20) = Z_to_bv 64 892832 -> getr R (reg 21) = Z_to_bv 64 89964 -> getr R (reg 22) = Z_to_bv 64 0 -> getr R (reg 23) = Z_to_bv 64 (V 33%nat) -> getr R (reg 25) = Z_to_bv 64 18446744073709551615 -> getr R (reg 26) = Z_to_bv 64 0 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 2224) 2272 -> L5.defined M ((V 2%nat) - 2224) 2272 ->
  L5.img_clear M 65536 880640 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 131071 -> (((V 2%nat) - 2224) + 2272 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 2224)) ->
  L5.writable RSEGS M 892872 8 -> L5.u8_at RSEGS M 892832 5 -> L5.u64_at RSEGS M 892864 ((V 2%nat) + 640) -> L5.u64_at RSEGS M 892872 ((V 2%nat) + 567) ->
  L5.u32_at RSEGS M 892976 4294967295 -> L5.u8_at RSEGS M 911385 1 -> L5.u64_at RSEGS M 882704 833320 -> L5.u8_at RSEGS M ((V 33%nat) + (V 34%nat)) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 2224) <= bv_unsigned a < ((V 2%nat) - 2224) + 2272) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 2224) <= i < ((V 2%nat) - 2224) + 2272) -> ~ (892872 <= i < 892872 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc4400 M) (st fx' R' 0xc494c M')
        /\ (forall x, In x KS_duD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 804904
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 892832
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 2%nat) + 567)
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 3
        /\ getr R' (reg 18) = Z_to_bv 64 0
        /\ getr R' (reg 24) = Z_to_bv 64 0
        /\ getr R' (reg 25) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 34%nat)
        /\ L5.u64_at RSEGS M' 892872 ((V 2%nat) + 567)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 32) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 16) (V 34%nat)
        /\ L5.u64_at RSEGS M' (V 2%nat) 68858
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 24) 0
        /\ L5.defined M' ((V 2%nat) + 40) 8).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G25 G26 [K0l K0r] K1 K2 K3 K4 [K5l K5r] [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PduD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduD.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduD.kn0).
  { unfold know_ok, PduD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7 HV34l HV34r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K5l K5r K7 HV34l HV34r K6l K6r; lia | clear - HV33l HV33r K5l K5r K7 HV34l HV34r K6l K6r; lia | byte_tac ltac:(clear) | exactA K15]. }
    apply Forall_nil. }
  destruct (PduD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PduD.NX0 with 140%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 2224) <= bv_unsigned a < ((V 2%nat) - 2224) + 2272) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PduD.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduD.ps0) with 0xc494c in Hms. change (SR.ps_regs PduD.ps0) with (map (fun i => (i, nth i PduD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduD.ps0) with PduD.cells0 in Hcells. unfold PduD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduD.regs0 PduD.regs_out0 140 KS_duD KS_duD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduD.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PduD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduDs := LibSegZ_duDs.
Definition KS_duDs : list nat := Eval vm_compute in (BG.kept_list 140 PduDs.regs0 PduDs.regs_out0).
Lemma KS_duDs_ok : BG.kept_ok 140 PduDs.regs0 PduDs.regs_out0 KS_duDs = true. Proof. vm_compute. reflexivity. Qed.
Lemma duDs_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 37 -> getr R (reg 9) = Z_to_bv 64 2147483647 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 892832 -> getr R (reg 18) = Z_to_bv 64 0 -> getr R (reg 19) = Z_to_bv 64 7 -> getr R (reg 20) = Z_to_bv 64 892832 -> getr R (reg 21) = Z_to_bv 64 89964 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.defined M ((V 2%nat) - 64) 64 ->
  L5.img_clear M 65536 880640 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 73 -> (((V 2%nat) - 64) + 64 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 64)) ->
  L5.u64_at RSEGS M 892864 ((V 2%nat) + 640) -> L5.u64_at RSEGS M 892872 ((V 2%nat) + 567) -> L5.u32_at RSEGS M 892976 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc494c M) (st fx' R' 0x5e0d0 M')
        /\ (forall x, In x KS_duDs -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 800936
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 892832
        /\ getr R' (reg 9) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 2%nat) + 567)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 89964
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 892832
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 7
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) 2147483647
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) 37
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) 805200
        /\ L5.defined M' ((V 2%nat) - 64) 8).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 [K0l K0r] K1 K2 K3 K4 [K5l K5r] [K6l K6r] K7 K8 K9 K10.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PduDs.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduDs.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduDs.kn0).
  { unfold know_ok, PduDs.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K10]. }
    apply Forall_nil. }
  destruct (PduDs.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PduDs.NX0 with 140%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PduDs.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduDs.ps0) with 0x5e0d0 in Hms. change (SR.ps_regs PduDs.ps0) with (map (fun i => (i, nth i PduDs.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduDs.ps0) with PduDs.cells0 in Hcells. unfold PduDs.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduDs.regs0 PduDs.regs_out0 140 KS_duDs KS_duDs_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDs.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduDs.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduDl := LibSegZ_duDl.
Definition KS_duDl : list nat := Eval vm_compute in (BG.kept_list 140 PduDl.regs0 PduDl.regs_out0).
Lemma KS_duDl_ok : BG.kept_ok 140 PduDl.regs0 PduDl.regs_out0 KS_duDl = true. Proof. vm_compute. reflexivity. Qed.
Lemma duDl_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 37 -> getr R (reg 9) = Z_to_bv 64 2147483647 -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) -> getr R (reg 12) = Z_to_bv 64 892832 -> getr R (reg 18) = Z_to_bv 64 0 -> getr R (reg 19) = Z_to_bv 64 7 -> getr R (reg 20) = Z_to_bv 64 892832 -> getr R (reg 21) = Z_to_bv 64 89964 -> getr R (reg 22) = Z_to_bv 64 0 ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 112) 112 -> L5.defined M ((V 2%nat) - 112) 112 ->
  L5.img_clear M 65536 880640 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 74 <= (V 34%nat) <= 131071 -> (((V 2%nat) - 112) + 112 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 112)) ->
  L5.u64_at RSEGS M 892864 ((V 2%nat) + 640) -> L5.u64_at RSEGS M 892872 ((V 2%nat) + 567) -> L5.u64_at RSEGS M 892904 798124 -> L5.u64_at RSEGS M 6491464 (V 40%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 112) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 112) <= i < ((V 2%nat) - 112) + 112) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc494c M) (st fx' R' 0xc2de8 M')
        /\ (forall x, In x KS_duDl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 805200
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 112)
        /\ getr R' (reg 6) = Z_to_bv 64 798124
        /\ getr R' (reg 8) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 892832
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 6491464
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 72) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) 89964
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) 892832
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) 7
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) 2147483647
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) 37
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) 805200
        /\ L5.defined M' ((V 2%nat) - 112) 40).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV40l HV40r] G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 [K0l K0r] K1 K2 K3 K4 [K5l K5r] [K6l K6r] K7 K8 K9 K10 K11.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 40%nat => (V 40%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PduDl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduDl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduDl.kn0).
  { unfold know_ok, PduDl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K11]. }
    apply Forall_nil. }
  destruct (PduDl.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PduDl.NX0 with 140%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 112) <= bv_unsigned a < ((V 2%nat) - 112) + 112) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PduDl.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduDl.ps0) with 0xc2de8 in Hms. change (SR.ps_regs PduDl.ps0) with (map (fun i => (i, nth i PduDl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduDl.ps0) with PduDl.cells0 in Hcells. unfold PduDl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduDl.regs0 PduDl.regs_out0 140 KS_duDl KS_duDl_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduDl.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduDl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduEa := LibSegZ_duEa.
Definition KS_duEa : list nat := Eval vm_compute in (BG.kept_list 140 PduEa.regs0 PduEa.regs_out0).
Lemma KS_duEa_ok : BG.kept_ok 140 PduEa.regs0 PduEa.regs_out0 KS_duEa = true. Proof. vm_compute. reflexivity. Qed.
Lemma duEa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 892832 -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 0 -> getr R (reg 26) = Z_to_bv 64 (V 34%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 80 -> L5.defined M ((V 2%nat) - 16) 80 ->
  L5.img_clear M 65536 880640 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 66 -> (((V 2%nat) - 16) + 80 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.writable RSEGS M 892872 8 -> L5.u64_at RSEGS M 892872 ((V 2%nat) + 631) -> L5.u64_at RSEGS M ((V 2%nat) + 56) 805200 -> L5.u64_at RSEGS M ((V 2%nat) + 48) 37 ->
  L5.u64_at RSEGS M ((V 2%nat) + 40) 2147483647 -> L5.u64_at RSEGS M ((V 2%nat) + 32) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 24) 7 -> L5.u64_at RSEGS M ((V 2%nat) + 16) 892832 ->
  L5.u64_at RSEGS M ((V 2%nat) + 8) 89964 -> L5.u8_at RSEGS M 892832 5 -> L5.u64_at RSEGS M 892864 ((V 2%nat) + 704) -> L5.u32_at RSEGS M 892976 4294967295 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 80) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 80) -> ~ (892872 <= i < 892872 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc38a8 M) (st fx' R' 0x5e0d0 M')
        /\ (forall x, In x KS_duEa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 800936
        /\ getr R' (reg 9) = Z_to_bv 64 7
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 2%nat) + (V 34%nat)) + 631)
        /\ getr R' (reg 11) = Z_to_bv 64 89964
        /\ getr R' (reg 12) = Z_to_bv 64 7
        /\ getr R' (reg 18) = Z_to_bv 64 89964
        /\ getr R' (reg 20) = Z_to_bv 64 892832
        /\ getr R' (reg 21) = Z_to_bv 64 89971
        /\ getr R' (reg 22) = Z_to_bv 64 7
        /\ getr R' (reg 23) = Z_to_bv 64 89964
        /\ getr R' (reg 26) = Z_to_bv 64 7
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) 89971
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 16) 892832
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 24) ((V 34%nat) + 7)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 32) (((-1) * (V 34%nat)) + 2147483640)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 40) 2147483647
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 48) 37
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 56) 802608
        /\ L5.u64_at RSEGS M' 892872 (((V 2%nat) + (V 34%nat)) + 631)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] G2 G8 G9 G19 G26 [K0l K0r] K1 K2 K3 K4 [K5l K5r] [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PduEa.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduEa.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduEa.kn0).
  { unfold know_ok, PduEa.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K19]. }
    apply Forall_nil. }
  destruct (PduEa.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PduEa.NX0 with 140%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 80) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PduEa.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduEa.ps0) with 0x5e0d0 in Hms. change (SR.ps_regs PduEa.ps0) with (map (fun i => (i, nth i PduEa.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduEa.ps0) with PduEa.cells0 in Hcells. unfold PduEa.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduEa.regs0 PduEa.regs_out0 140 KS_duEa KS_duEa_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEa.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduEa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 HV34l HV34r K6l K6r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduEb := LibSegZ_duEb.
Definition KS_duEb : list nat := Eval vm_compute in (BG.kept_list 140 PduEb.regs0 PduEb.regs_out0).
Lemma KS_duEb_ok : BG.kept_ok 140 PduEb.regs0 PduEb.regs_out0 KS_duEb = true. Proof. vm_compute. reflexivity. Qed.
Lemma duEb_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 892832 -> getr R (reg 9) = Z_to_bv 64 (V 34%nat) -> getr R (reg 19) = Z_to_bv 64 0 -> getr R (reg 26) = Z_to_bv 64 (V 34%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 48) 112 -> L5.defined M ((V 2%nat) - 48) 112 ->
  L5.img_clear M 65536 880640 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 67 <= (V 34%nat) <= 73 -> (((V 2%nat) - 48) + 112 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 48)) ->
  L5.writable RSEGS M 892872 8 -> L5.u64_at RSEGS M 892872 ((V 2%nat) + 631) -> L5.u64_at RSEGS M ((V 2%nat) + 56) 805200 -> L5.u64_at RSEGS M ((V 2%nat) + 48) 37 ->
  L5.u64_at RSEGS M ((V 2%nat) + 40) 2147483647 -> L5.u64_at RSEGS M ((V 2%nat) + 32) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 24) 7 -> L5.u64_at RSEGS M ((V 2%nat) + 16) 892832 ->
  L5.u64_at RSEGS M ((V 2%nat) + 8) 89964 -> L5.u8_at RSEGS M 892832 5 -> L5.u64_at RSEGS M 892864 ((V 2%nat) + 704) -> L5.u64_at RSEGS M 892904 798124 ->
  L5.u64_at RSEGS M 6491464 (V 40%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 112) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 48) <= i < ((V 2%nat) - 48) + 112) -> ~ (892872 <= i < 892872 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc38a8 M) (st fx' R' 0xc2de8 M')
        /\ (forall x, In x KS_duEb -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 802608
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 48)
        /\ getr R' (reg 6) = Z_to_bv 64 798124
        /\ getr R' (reg 8) = Z_to_bv 64 7
        /\ getr R' (reg 9) = Z_to_bv 64 892832
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 89964
        /\ getr R' (reg 12) = Z_to_bv 64 7
        /\ getr R' (reg 18) = Z_to_bv 64 (((-1) * (V 34%nat)) + 2147483640)
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 34%nat) + 7)
        /\ getr R' (reg 20) = Z_to_bv 64 892832
        /\ getr R' (reg 21) = Z_to_bv 64 6491464
        /\ getr R' (reg 22) = Z_to_bv 64 7
        /\ getr R' (reg 23) = Z_to_bv 64 89964
        /\ getr R' (reg 26) = Z_to_bv 64 7
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (V 40%nat)
        /\ L5.u64_at RSEGS M' (V 2%nat) 7
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) 89971
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 16) 892832
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 24) ((V 34%nat) + 7)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 32) (((-1) * (V 34%nat)) + 2147483640)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 40) 2147483647
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 48) 37
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 56) 802608
        /\ L5.u64_at RSEGS M' 892872 (((V 2%nat) + (V 34%nat)) + 631)
        /\ L5.defined M' ((V 2%nat) - 48) 40).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV40l HV40r] G2 G8 G9 G19 G26 [K0l K0r] K1 K2 K3 K4 [K5l K5r] [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 40%nat => (V 40%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E PduEb.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduEb.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduEb.kn0).
  { unfold know_ok, PduEb.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K20]. }
    apply Forall_nil. }
  destruct (PduEb.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PduEb.NX0 with 140%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 48) <= bv_unsigned a < ((V 2%nat) - 48) + 112) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PduEb.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduEb.ps0) with 0xc2de8 in Hms. change (SR.ps_regs PduEb.ps0) with (map (fun i => (i, nth i PduEb.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduEb.ps0) with PduEb.cells0 in Hcells. unfold PduEb.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduEb.regs0 PduEb.regs_out0 140 KS_duEb KS_duEb_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 6 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEb.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduEb.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 HV34l HV34r K6l K6r) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduFa := LibSegZ_duFa.
Definition KS_duFa : list nat := Eval vm_compute in (BG.kept_list 140 PduFa.regs0 PduFa.regs_out0).
Lemma KS_duFa_ok : BG.kept_ok 140 PduFa.regs0 PduFa.regs_out0 KS_duFa = true. Proof. vm_compute. reflexivity. Qed.
Lemma duFa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 23%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 25%nat) < 2 ^ 64 -> 0 <= (V 26%nat) < 2 ^ 64 -> 0 <= (V 27%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 123%nat) < 2 ^ 64 -> 0 <= (V 124%nat) < 2 ^ 64 -> 0 <= (V 125%nat) < 2 ^ 64 -> 0 <= (V 127%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 892832 -> getr R (reg 9) = Z_to_bv 64 7 -> getr R (reg 19) = Z_to_bv 64 0 -> getr R (reg 22) = Z_to_bv 64 7 -> getr R (reg 23) = Z_to_bv 64 (V 123%nat) -> getr R (reg 24) = Z_to_bv 64 (V 124%nat) -> getr R (reg 25) = Z_to_bv 64 (V 125%nat) -> getr R (reg 26) = Z_to_bv 64 7 -> getr R (reg 27) = Z_to_bv 64 (V 127%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 624 -> L5.defined M ((V 2%nat) - 16) 624 ->
  L5.img_clear M 65536 880640 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 66 -> (((V 2%nat) - 16) + 624 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.writable RSEGS M 892872 8 -> L5.u64_at RSEGS M 892872 (((V 2%nat) + (V 34%nat)) + 631) -> L5.u64_at RSEGS M ((V 2%nat) + 56) 802608 -> L5.u64_at RSEGS M ((V 2%nat) + 48) 37 ->
  L5.u64_at RSEGS M ((V 2%nat) + 40) 2147483647 -> L5.u64_at RSEGS M ((V 2%nat) + 32) (2147483640 - (V 34%nat)) -> L5.u64_at RSEGS M ((V 2%nat) + 24) ((V 34%nat) + 7) -> L5.u64_at RSEGS M ((V 2%nat) + 16) 892832 ->
  L5.u64_at RSEGS M ((V 2%nat) + 8) 89971 -> L5.u64_at RSEGS M ((V 2%nat) + 160) 6491464 -> L5.u64_at RSEGS M 6491464 (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 496) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 600) 802112 -> L5.u64_at RSEGS M ((V 2%nat) + 592) 892832 -> L5.u64_at RSEGS M ((V 2%nat) + 584) 89955 -> L5.u64_at RSEGS M ((V 2%nat) + 576) 6491464 ->
  L5.u64_at RSEGS M ((V 2%nat) + 568) 1 -> L5.u64_at RSEGS M ((V 2%nat) + 560) 6493200 -> L5.u64_at RSEGS M ((V 2%nat) + 552) 5 -> L5.u64_at RSEGS M ((V 2%nat) + 544) (V 22%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 536) (V 23%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 528) (V 24%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 520) (V 25%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 512) (V 26%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 504) (V 27%nat) -> L5.u64_at RSEGS M 892904 798124 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 624) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 624) -> ~ (892872 <= i < 892872 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc38a8 M) (st fx' R' 0xc2de8 M')
        /\ (forall x, In x KS_duFa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 802144
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 496)
        /\ getr R' (reg 8) = Z_to_bv 64 0
        /\ getr R' (reg 9) = Z_to_bv 64 892832
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 798124
        /\ getr R' (reg 18) = Z_to_bv 64 6491464
        /\ getr R' (reg 19) = Z_to_bv 64 1
        /\ getr R' (reg 20) = Z_to_bv 64 6493200
        /\ getr R' (reg 21) = Z_to_bv 64 6491464
        /\ getr R' (reg 22) = Z_to_bv 64 (V 22%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 23%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 25%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 26%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 27%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 536) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 544) (V 22%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 552) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 560) 6493200
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 568) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 576) 6491464
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 584) ((V 34%nat) + 14)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 592) 892832
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 600) 802144
        /\ L5.u64_at RSEGS M' 892872 (((V 2%nat) + (V 34%nat)) + 638)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 496) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 528) (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 520) (V 25%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 512) (V 26%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 504) (V 27%nat)).
Proof.
  intros [HV2l HV2r] [HV22l HV22r] [HV23l HV23r] [HV24l HV24r] [HV25l HV25r] [HV26l HV26r] [HV27l HV27r] [HV33l HV33r] [HV34l HV34r] [HV40l HV40r] [HV123l HV123r] [HV124l HV124r] [HV125l HV125r] [HV127l HV127r] G2 G8 G9 G19 G22 G23 G24 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 [K5l K5r] [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 22%nat => Z_to_bv 64 (V 22%nat) | 23%nat => Z_to_bv 64 (V 23%nat) | 24%nat => Z_to_bv 64 (V 24%nat) | 25%nat => Z_to_bv 64 (V 25%nat) | 26%nat => Z_to_bv 64 (V 26%nat) | 27%nat => Z_to_bv 64 (V 27%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 123%nat => Z_to_bv 64 (V 123%nat) | 124%nat => Z_to_bv 64 (V 124%nat) | 125%nat => Z_to_bv 64 (V 125%nat) | 127%nat => Z_to_bv 64 (V 127%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 22%nat => (V 22%nat) | 23%nat => (V 23%nat) | 24%nat => (V 24%nat) | 25%nat => (V 25%nat) | 26%nat => (V 26%nat) | 27%nat => (V 27%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 40%nat => (V 40%nat) | 123%nat => (V 123%nat) | 124%nat => (V 124%nat) | 125%nat => (V 125%nat) | 127%nat => (V 127%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 128%nat. }
  assert (HR: regs_ok E PduFa.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduFa.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduFa.kn0).
  { unfold know_ok, PduFa.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7 HV34l HV34r K6l K6r) | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV22l HV22r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV23l HV23r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV25l HV25r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV26l HV26r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV27l HV27r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K33]. }
    apply Forall_nil. }
  destruct (PduFa.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PduFa.NX0 with 140%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 624) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PduFa.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduFa.ps0) with 0xc2de8 in Hms. change (SR.ps_regs PduFa.ps0) with (map (fun i => (i, nth i PduFa.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduFa.ps0) with PduFa.cells0 in Hcells. unfold PduFa.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduFa.regs0 PduFa.regs_out0 140 KS_duFa KS_duFa_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduFa.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PduFa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV22l HV22r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7 HV34l HV34r K6l K6r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV24l HV24r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV25l HV25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV26l HV26r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV27l HV27r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduGa := LibSegZ_duGa.
Definition KS_duGa : list nat := Eval vm_compute in (BG.kept_list 140 PduGa.regs0 PduGa.regs_out0).
Lemma KS_duGa_ok : BG.kept_ok 140 PduGa.regs0 PduGa.regs_out0 KS_duGa = true. Proof. vm_compute. reflexivity. Qed.
Lemma duGa_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 20%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 118%nat) < 2 ^ 64 -> 0 <= (V 119%nat) < 2 ^ 64 -> 0 <= (V 120%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 9) = Z_to_bv 64 892832 -> getr R (reg 18) = Z_to_bv 64 (V 118%nat) -> getr R (reg 19) = Z_to_bv 64 (V 119%nat) -> getr R (reg 20) = Z_to_bv 64 (V 120%nat) -> getr R (reg 21) = Z_to_bv 64 6491464 -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.defined M ((V 2%nat) - 16) 16 ->
  L5.img_clear M 65536 880640 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 0 <= (V 34%nat) <= 66 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.writable RSEGS M 892832 4 -> L5.writable RSEGS M 892864 8 -> L5.writable RSEGS M 892872 8 -> L5.writable RSEGS M 892888 8 ->
  L5.writable RSEGS M 892920 8 -> L5.writable RSEGS M 892928 8 -> L5.u64_at RSEGS M 892920 ((V 2%nat) + 128) -> L5.u64_at RSEGS M 892928 80 ->
  L5.u64_at RSEGS M 6491464 (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 40) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 104) 802144 -> L5.u64_at RSEGS M ((V 2%nat) + 96) 892832 ->
  L5.u64_at RSEGS M ((V 2%nat) + 88) ((V 34%nat) + 14) -> L5.u64_at RSEGS M ((V 2%nat) + 80) 6491464 -> L5.u64_at RSEGS M ((V 2%nat) + 72) 1 -> L5.u64_at RSEGS M ((V 2%nat) + 64) 6493200 ->
  L5.u64_at RSEGS M ((V 2%nat) + 56) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 48) (V 22%nat) -> L5.u32_at RSEGS M 892832 5 -> L5.u64_at RSEGS M ((V 2%nat) + 416) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 472) 332964 -> L5.u64_at RSEGS M ((V 2%nat) + 464) 89955 -> L5.u64_at RSEGS M ((V 2%nat) + 456) 892832 -> L5.u64_at RSEGS M ((V 2%nat) + 448) ((V 2%nat) + 544) ->
  L5.u64_at RSEGS M ((V 2%nat) + 440) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 432) (V 20%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 424) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 536) 580508 ->
  L5.u64_at RSEGS M ((V 2%nat) + 528) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 520) (V 9%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 512) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 664) 773476 ->
  L5.u64_at RSEGS M ((V 2%nat) + 656) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 648) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 640) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 632) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 624) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 616) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 608) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 600) (V 48%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (892832 <= bv_unsigned a < 892832 + 4) -> ~ (892864 <= bv_unsigned a < 892864 + 8) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> ~ (892888 <= bv_unsigned a < 892888 + 8) -> ~ (892920 <= bv_unsigned a < 892920 + 8) -> ~ (892928 <= bv_unsigned a < 892928 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> ~ (892832 <= i < 892832 + 4) -> ~ (892864 <= i < 892864 + 8) -> ~ (892872 <= i < 892872 + 8) -> ~ (892888 <= i < 892888 + 8) -> ~ (892920 <= i < 892920 + 8) -> ~ (892928 <= i < 892928 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc2e40 M) (st fx' R' 0xbd464 M')
        /\ (forall x, In x KS_duGa -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 773480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 672)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 48%nat)
        /\ L5.u32_at RSEGS M' 892832 5
        /\ L5.u64_at RSEGS M' 892928 0
        /\ L5.u64_at RSEGS M' 892920 6493200
        /\ L5.u64_at RSEGS M' 892888 0
        /\ L5.u64_at RSEGS M' 892872 0
        /\ L5.u64_at RSEGS M' 892864 0).
Proof.
  intros [HV2l HV2r] [HV8l HV8r] [HV9l HV9r] [HV18l HV18r] [HV19l HV19r] [HV20l HV20r] [HV21l HV21r] [HV22l HV22r] [HV33l HV33r] [HV34l HV34r] [HV40l HV40r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV118l HV118r] [HV119l HV119r] [HV120l HV120r] [HV122l HV122r] G2 G8 G9 G18 G19 G20 G21 G22 [K0l K0r] K1 K2 K3 K4 [K5l K5r] [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 8%nat => Z_to_bv 64 (V 8%nat) | 9%nat => Z_to_bv 64 (V 9%nat) | 18%nat => Z_to_bv 64 (V 18%nat) | 19%nat => Z_to_bv 64 (V 19%nat) | 20%nat => Z_to_bv 64 (V 20%nat) | 21%nat => Z_to_bv 64 (V 21%nat) | 22%nat => Z_to_bv 64 (V 22%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 118%nat => Z_to_bv 64 (V 118%nat) | 119%nat => Z_to_bv 64 (V 119%nat) | 120%nat => Z_to_bv 64 (V 120%nat) | 122%nat => Z_to_bv 64 (V 122%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 8%nat => (V 8%nat) | 9%nat => (V 9%nat) | 18%nat => (V 18%nat) | 19%nat => (V 19%nat) | 20%nat => (V 20%nat) | 21%nat => (V 21%nat) | 22%nat => (V 22%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 118%nat => (V 118%nat) | 119%nat => (V 119%nat) | 120%nat => (V 120%nat) | 122%nat => (V 122%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 123%nat. }
  assert (HR: regs_ok E PduGa.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduGa.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduGa.kn0).
  { unfold know_ok, PduGa.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV22l HV22r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV20l HV20r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV8l HV8r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV9l HV9r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV18l HV18r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K47]. }
    apply Forall_nil. }
  destruct (PduGa.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PduGa.NX0 with 140%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (892832 <= bv_unsigned a < 892832 + 4) -> ~ (892864 <= bv_unsigned a < 892864 + 8) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> ~ (892888 <= bv_unsigned a < 892888 + 8) -> ~ (892920 <= bv_unsigned a < 892920 + 8) -> ~ (892928 <= bv_unsigned a < 892928 + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply Hfr. unfold PduGa.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn6; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduGa.ps0) with 0xbd464 in Hms. change (SR.ps_regs PduGa.ps0) with (map (fun i => (i, nth i PduGa.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduGa.ps0) with PduGa.cells0 in Hcells. unfold PduGa.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduGa.regs0 PduGa.regs_out0 140 KS_duGa KS_duGa_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGa.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduGa.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduGb1 := LibSegZ_duGb1.
Definition KS_duGb1 : list nat := Eval vm_compute in (BG.kept_list 140 PduGb1.regs0 PduGb1.regs_out0).
Lemma KS_duGb1_ok : BG.kept_ok 140 PduGb1.regs0 PduGb1.regs_out0 KS_duGb1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma duGb1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 23%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 25%nat) < 2 ^ 64 -> 0 <= (V 26%nat) < 2 ^ 64 -> 0 <= (V 27%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 -> 0 <= (V 123%nat) < 2 ^ 64 -> 0 <= (V 124%nat) < 2 ^ 64 -> 0 <= (V 125%nat) < 2 ^ 64 -> 0 <= (V 127%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 7 -> getr R (reg 9) = Z_to_bv 64 892832 -> getr R (reg 21) = Z_to_bv 64 6491464 -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) -> getr R (reg 23) = Z_to_bv 64 (V 123%nat) -> getr R (reg 24) = Z_to_bv 64 (V 124%nat) -> getr R (reg 25) = Z_to_bv 64 (V 125%nat) -> getr R (reg 26) = Z_to_bv 64 7 -> getr R (reg 27) = Z_to_bv 64 (V 127%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 672 -> L5.defined M ((V 2%nat) - 16) 672 ->
  L5.img_clear M 65536 880640 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 67 <= (V 34%nat) <= 73 -> (((V 2%nat) - 16) + 672 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.writable RSEGS M 892864 8 -> L5.writable RSEGS M 892872 8 -> L5.writable RSEGS M 892888 8 -> L5.u64_at RSEGS M 892920 ((V 2%nat) + 672) ->
  L5.u64_at RSEGS M 892928 80 -> L5.u64_at RSEGS M 6491464 (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 40) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 104) 802608 ->
  L5.u64_at RSEGS M ((V 2%nat) + 96) 37 -> L5.u64_at RSEGS M ((V 2%nat) + 88) 2147483647 -> L5.u64_at RSEGS M ((V 2%nat) + 80) (2147483640 - (V 34%nat)) -> L5.u64_at RSEGS M ((V 2%nat) + 72) ((V 34%nat) + 7) ->
  L5.u64_at RSEGS M ((V 2%nat) + 64) 892832 -> L5.u64_at RSEGS M ((V 2%nat) + 56) 89971 -> L5.u64_at RSEGS M ((V 2%nat) + 48) 7 -> L5.u64_at RSEGS M ((V 2%nat) + 208) 6491464 ->
  L5.u64_at RSEGS M ((V 2%nat) + 544) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 648) 802112 -> L5.u64_at RSEGS M ((V 2%nat) + 640) 892832 -> L5.u64_at RSEGS M ((V 2%nat) + 632) 89955 ->
  L5.u64_at RSEGS M ((V 2%nat) + 624) 6491464 -> L5.u64_at RSEGS M ((V 2%nat) + 616) 1 -> L5.u64_at RSEGS M ((V 2%nat) + 608) 6493200 -> L5.u64_at RSEGS M ((V 2%nat) + 600) 5 ->
  L5.u64_at RSEGS M ((V 2%nat) + 592) (V 22%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 584) (V 23%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 576) (V 24%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 568) (V 25%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 560) (V 26%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 552) (V 27%nat) -> L5.u64_at RSEGS M 892904 798124 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 672) -> ~ (892864 <= bv_unsigned a < 892864 + 8) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> ~ (892888 <= bv_unsigned a < 892888 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 672) -> ~ (892864 <= i < 892864 + 8) -> ~ (892872 <= i < 892872 + 8) -> ~ (892888 <= i < 892888 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc2e40 M) (st fx' R' 0xc2de8 M')
        /\ (forall x, In x KS_duGb1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 802144
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 544)
        /\ getr R' (reg 8) = Z_to_bv 64 0
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 798124
        /\ getr R' (reg 18) = Z_to_bv 64 6491464
        /\ getr R' (reg 19) = Z_to_bv 64 1
        /\ getr R' (reg 20) = Z_to_bv 64 6493200
        /\ getr R' (reg 22) = Z_to_bv 64 (V 22%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 23%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 25%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 26%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 27%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 584) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 592) (V 22%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 600) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 608) 6493200
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 616) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 624) 6491464
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 632) ((V 34%nat) + 14)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 640) 892832
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 648) 802144
        /\ L5.u64_at RSEGS M' 892888 ((V 2%nat) + 672)
        /\ L5.u64_at RSEGS M' 892872 ((V 2%nat) + 672)
        /\ L5.u64_at RSEGS M' 892864 ((V 2%nat) + 752)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 544) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 576) (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 568) (V 25%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 560) (V 26%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 552) (V 27%nat)).
Proof.
  intros [HV2l HV2r] [HV22l HV22r] [HV23l HV23r] [HV24l HV24r] [HV25l HV25r] [HV26l HV26r] [HV27l HV27r] [HV33l HV33r] [HV34l HV34r] [HV40l HV40r] [HV122l HV122r] [HV123l HV123r] [HV124l HV124r] [HV125l HV125r] [HV127l HV127r] G2 G8 G9 G21 G22 G23 G24 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 [K5l K5r] [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 22%nat => Z_to_bv 64 (V 22%nat) | 23%nat => Z_to_bv 64 (V 23%nat) | 24%nat => Z_to_bv 64 (V 24%nat) | 25%nat => Z_to_bv 64 (V 25%nat) | 26%nat => Z_to_bv 64 (V 26%nat) | 27%nat => Z_to_bv 64 (V 27%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 122%nat => Z_to_bv 64 (V 122%nat) | 123%nat => Z_to_bv 64 (V 123%nat) | 124%nat => Z_to_bv 64 (V 124%nat) | 125%nat => Z_to_bv 64 (V 125%nat) | 127%nat => Z_to_bv 64 (V 127%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 22%nat => (V 22%nat) | 23%nat => (V 23%nat) | 24%nat => (V 24%nat) | 25%nat => (V 25%nat) | 26%nat => (V 26%nat) | 27%nat => (V 27%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 40%nat => (V 40%nat) | 122%nat => (V 122%nat) | 123%nat => (V 123%nat) | 124%nat => (V 124%nat) | 125%nat => (V 125%nat) | 127%nat => (V 127%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 128%nat. }
  assert (HR: regs_ok E PduGb1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduGb1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduGb1.kn0).
  { unfold know_ok, PduGb1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV22l HV22r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV23l HV23r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV25l HV25r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV26l HV26r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV27l HV27r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K38]. }
    apply Forall_nil. }
  destruct (PduGb1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PduGb1.NX0 with 140%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 672) -> ~ (892864 <= bv_unsigned a < 892864 + 8) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> ~ (892888 <= bv_unsigned a < 892888 + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PduGb1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduGb1.ps0) with 0xc2de8 in Hms. change (SR.ps_regs PduGb1.ps0) with (map (fun i => (i, nth i PduGb1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduGb1.ps0) with PduGb1.cells0 in Hcells. unfold PduGb1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduGb1.regs0 PduGb1.regs_out0 140 KS_duGb1 KS_duGb1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb1.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PduGb1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV22l HV22r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV24l HV24r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV25l HV25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV26l HV26r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV27l HV27r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduGb2 := LibSegZ_duGb2.
Definition KS_duGb2 : list nat := Eval vm_compute in (BG.kept_list 140 PduGb2.regs0 PduGb2.regs_out0).
Lemma KS_duGb2_ok : BG.kept_ok 140 PduGb2.regs0 PduGb2.regs_out0 KS_duGb2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma duGb2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 20%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 118%nat) < 2 ^ 64 -> 0 <= (V 119%nat) < 2 ^ 64 -> 0 <= (V 120%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 9) = Z_to_bv 64 892832 -> getr R (reg 18) = Z_to_bv 64 (V 118%nat) -> getr R (reg 19) = Z_to_bv 64 (V 119%nat) -> getr R (reg 20) = Z_to_bv 64 (V 120%nat) -> getr R (reg 21) = Z_to_bv 64 6491464 -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.defined M ((V 2%nat) - 16) 16 ->
  L5.img_clear M 65536 880640 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 67 <= (V 34%nat) <= 73 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.writable RSEGS M 892832 4 -> L5.writable RSEGS M 892864 8 -> L5.writable RSEGS M 892872 8 -> L5.writable RSEGS M 892888 8 ->
  L5.writable RSEGS M 892920 8 -> L5.writable RSEGS M 892928 8 -> L5.u64_at RSEGS M 892920 ((V 2%nat) + 128) -> L5.u64_at RSEGS M 892928 80 ->
  L5.u64_at RSEGS M 6491464 (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 40) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 104) 802144 -> L5.u64_at RSEGS M ((V 2%nat) + 96) 892832 ->
  L5.u64_at RSEGS M ((V 2%nat) + 88) ((V 34%nat) + 14) -> L5.u64_at RSEGS M ((V 2%nat) + 80) 6491464 -> L5.u64_at RSEGS M ((V 2%nat) + 72) 1 -> L5.u64_at RSEGS M ((V 2%nat) + 64) 6493200 ->
  L5.u64_at RSEGS M ((V 2%nat) + 56) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 48) (V 22%nat) -> L5.u32_at RSEGS M 892832 5 -> L5.u64_at RSEGS M ((V 2%nat) + 416) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 472) 332964 -> L5.u64_at RSEGS M ((V 2%nat) + 464) 89955 -> L5.u64_at RSEGS M ((V 2%nat) + 456) 892832 -> L5.u64_at RSEGS M ((V 2%nat) + 448) ((V 2%nat) + 544) ->
  L5.u64_at RSEGS M ((V 2%nat) + 440) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 432) (V 20%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 424) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 536) 580508 ->
  L5.u64_at RSEGS M ((V 2%nat) + 528) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 520) (V 9%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 512) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 664) 773476 ->
  L5.u64_at RSEGS M ((V 2%nat) + 656) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 648) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 640) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 632) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 624) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 616) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 608) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 600) (V 48%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (892832 <= bv_unsigned a < 892832 + 4) -> ~ (892864 <= bv_unsigned a < 892864 + 8) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> ~ (892888 <= bv_unsigned a < 892888 + 8) -> ~ (892920 <= bv_unsigned a < 892920 + 8) -> ~ (892928 <= bv_unsigned a < 892928 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> ~ (892832 <= i < 892832 + 4) -> ~ (892864 <= i < 892864 + 8) -> ~ (892872 <= i < 892872 + 8) -> ~ (892888 <= i < 892888 + 8) -> ~ (892920 <= i < 892920 + 8) -> ~ (892928 <= i < 892928 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc2e40 M) (st fx' R' 0xbd464 M')
        /\ (forall x, In x KS_duGb2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 773480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 672)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 48%nat)
        /\ L5.u32_at RSEGS M' 892832 5
        /\ L5.u64_at RSEGS M' 892928 0
        /\ L5.u64_at RSEGS M' 892920 6493200
        /\ L5.u64_at RSEGS M' 892888 0
        /\ L5.u64_at RSEGS M' 892872 0
        /\ L5.u64_at RSEGS M' 892864 0).
Proof.
  intros [HV2l HV2r] [HV8l HV8r] [HV9l HV9r] [HV18l HV18r] [HV19l HV19r] [HV20l HV20r] [HV21l HV21r] [HV22l HV22r] [HV33l HV33r] [HV34l HV34r] [HV40l HV40r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV118l HV118r] [HV119l HV119r] [HV120l HV120r] [HV122l HV122r] G2 G8 G9 G18 G19 G20 G21 G22 [K0l K0r] K1 K2 K3 K4 [K5l K5r] [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 8%nat => Z_to_bv 64 (V 8%nat) | 9%nat => Z_to_bv 64 (V 9%nat) | 18%nat => Z_to_bv 64 (V 18%nat) | 19%nat => Z_to_bv 64 (V 19%nat) | 20%nat => Z_to_bv 64 (V 20%nat) | 21%nat => Z_to_bv 64 (V 21%nat) | 22%nat => Z_to_bv 64 (V 22%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 118%nat => Z_to_bv 64 (V 118%nat) | 119%nat => Z_to_bv 64 (V 119%nat) | 120%nat => Z_to_bv 64 (V 120%nat) | 122%nat => Z_to_bv 64 (V 122%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 8%nat => (V 8%nat) | 9%nat => (V 9%nat) | 18%nat => (V 18%nat) | 19%nat => (V 19%nat) | 20%nat => (V 20%nat) | 21%nat => (V 21%nat) | 22%nat => (V 22%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 118%nat => (V 118%nat) | 119%nat => (V 119%nat) | 120%nat => (V 120%nat) | 122%nat => (V 122%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 123%nat. }
  assert (HR: regs_ok E PduGb2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduGb2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduGb2.kn0).
  { unfold know_ok, PduGb2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV22l HV22r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV20l HV20r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV8l HV8r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV9l HV9r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV18l HV18r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K47]. }
    apply Forall_nil. }
  destruct (PduGb2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PduGb2.NX0 with 140%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (892832 <= bv_unsigned a < 892832 + 4) -> ~ (892864 <= bv_unsigned a < 892864 + 8) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> ~ (892888 <= bv_unsigned a < 892888 + 8) -> ~ (892920 <= bv_unsigned a < 892920 + 8) -> ~ (892928 <= bv_unsigned a < 892928 + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply Hfr. unfold PduGb2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn6; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduGb2.ps0) with 0xbd464 in Hms. change (SR.ps_regs PduGb2.ps0) with (map (fun i => (i, nth i PduGb2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduGb2.ps0) with PduGb2.cells0 in Hcells. unfold PduGb2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduGb2.regs0 PduGb2.regs_out0 140 KS_duGb2 KS_duGb2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGb2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduGb2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduEc := LibSegZ_duEc.
Definition KS_duEc : list nat := Eval vm_compute in (BG.kept_list 140 PduEc.regs0 PduEc.regs_out0).
Lemma KS_duEc_ok : BG.kept_ok 140 PduEc.regs0 PduEc.regs_out0 KS_duEc = true. Proof. vm_compute. reflexivity. Qed.
Lemma duEc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 23%nat) < 2 ^ 64 -> 0 <= (V 24%nat) < 2 ^ 64 -> 0 <= (V 25%nat) < 2 ^ 64 -> 0 <= (V 26%nat) < 2 ^ 64 -> 0 <= (V 27%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 -> 0 <= (V 123%nat) < 2 ^ 64 -> 0 <= (V 125%nat) < 2 ^ 64 -> 0 <= (V 127%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 (V 34%nat) -> getr R (reg 9) = Z_to_bv 64 892832 -> getr R (reg 21) = Z_to_bv 64 6491464 -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) -> getr R (reg 23) = Z_to_bv 64 (V 123%nat) -> getr R (reg 24) = Z_to_bv 64 0 -> getr R (reg 25) = Z_to_bv 64 (V 125%nat) -> getr R (reg 26) = Z_to_bv 64 (V 34%nat) -> getr R (reg 27) = Z_to_bv 64 (V 127%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 2112) 2800 -> L5.defined M ((V 2%nat) - 2112) 2800 ->
  L5.img_clear M 65536 880640 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 74 <= (V 34%nat) <= 131071 -> (((V 2%nat) - 2112) + 2800 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 2112)) ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147450950) 24 -> L5.u64_at RSEGS M 2147462120 0 -> L5.writable RSEGS M 892864 8 -> L5.writable RSEGS M 892872 8 ->
  L5.writable RSEGS M 892888 8 -> L5.u64_at RSEGS M 892920 ((V 2%nat) + 672) -> L5.u64_at RSEGS M 892928 80 -> L5.u64_at RSEGS M 6491464 (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 40) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 104) 805200 -> L5.u64_at RSEGS M ((V 2%nat) + 96) 37 -> L5.u64_at RSEGS M ((V 2%nat) + 88) 2147483647 ->
  L5.u64_at RSEGS M ((V 2%nat) + 80) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 72) 7 -> L5.u64_at RSEGS M ((V 2%nat) + 64) 892832 -> L5.u64_at RSEGS M ((V 2%nat) + 56) 89964 ->
  L5.u64_at RSEGS M ((V 2%nat) + 48) 0 -> L5.u8_at RSEGS M 892832 5 -> L5.u32_at RSEGS M 892976 4294967295 -> L5.u8_at RSEGS M 911385 1 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u64_at RSEGS M 882704 833320 -> L5.u64_at RSEGS M ((V 2%nat) + 208) 6491464 -> L5.u64_at RSEGS M ((V 2%nat) + 544) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 648) 802112 -> L5.u64_at RSEGS M ((V 2%nat) + 640) 892832 -> L5.u64_at RSEGS M ((V 2%nat) + 632) 89955 -> L5.u64_at RSEGS M ((V 2%nat) + 624) 6491464 ->
  L5.u64_at RSEGS M ((V 2%nat) + 616) 1 -> L5.u64_at RSEGS M ((V 2%nat) + 608) 6493200 -> L5.u64_at RSEGS M ((V 2%nat) + 600) 5 -> L5.u64_at RSEGS M ((V 2%nat) + 592) (V 22%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 584) (V 23%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 576) (V 24%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 568) (V 25%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 560) (V 26%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 552) (V 27%nat) -> L5.u64_at RSEGS M 892904 798124 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 2112) <= bv_unsigned a < ((V 2%nat) - 2112) + 2800) -> ~ (892864 <= bv_unsigned a < 892864 + 8) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> ~ (892888 <= bv_unsigned a < 892888 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 2112) <= i < ((V 2%nat) - 2112) + 2800) -> ~ (892864 <= i < 892864 + 8) -> ~ (892872 <= i < 892872 + 8) -> ~ (892888 <= i < 892888 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc2e40 M) (st fx' R' 0xc2de8 M')
        /\ (forall x, In x KS_duEc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 802144
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 544)
        /\ getr R' (reg 8) = Z_to_bv 64 0
        /\ getr R' (reg 10) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 798124
        /\ getr R' (reg 14) = Z_to_bv 64 85
        /\ getr R' (reg 15) = Z_to_bv 64 84
        /\ getr R' (reg 16) = Z_to_bv 64 ((V 2%nat) + 678)
        /\ getr R' (reg 18) = Z_to_bv 64 6491464
        /\ getr R' (reg 19) = Z_to_bv 64 1
        /\ getr R' (reg 20) = Z_to_bv 64 6493200
        /\ getr R' (reg 22) = Z_to_bv 64 (V 22%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 23%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 24%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 25%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 26%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 27%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 584) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 592) (V 22%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 600) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 608) 6493200
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 616) 1
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 624) 6491464
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 632) ((V 34%nat) + 14)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 640) 892832
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 648) 802144
        /\ L5.u64_at RSEGS M' 892872 ((V 2%nat) + 679)
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 678) 10
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 677) 84
        /\ L5.u8_at RSEGS M' ((V 2%nat) + 676) 85
        /\ L5.u32_at RSEGS M' ((V 2%nat) + 672) 1347307808
        /\ L5.u64_at RSEGS M' 892888 ((V 2%nat) + 672)
        /\ L5.u64_at RSEGS M' 892864 ((V 2%nat) + 752)
        /\ L5.defined M' ((V 2%nat) + 656) 16
        /\ L5.defined M' ((V 2%nat) + 679) 9
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 544) (V 40%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 576) (V 24%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 568) (V 25%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 560) (V 26%nat)
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 552) (V 27%nat)).
Proof.
  intros [HV2l HV2r] [HV22l HV22r] [HV23l HV23r] [HV24l HV24r] [HV25l HV25r] [HV26l HV26r] [HV27l HV27r] [HV33l HV33r] [HV34l HV34r] [HV40l HV40r] [HV122l HV122r] [HV123l HV123r] [HV125l HV125r] [HV127l HV127r] G2 G8 G9 G21 G22 G23 G24 G25 G26 G27 [K0l K0r] K1 K2 K3 K4 [K5l K5r] [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 22%nat => Z_to_bv 64 (V 22%nat) | 23%nat => Z_to_bv 64 (V 23%nat) | 24%nat => Z_to_bv 64 (V 24%nat) | 25%nat => Z_to_bv 64 (V 25%nat) | 26%nat => Z_to_bv 64 (V 26%nat) | 27%nat => Z_to_bv 64 (V 27%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 122%nat => Z_to_bv 64 (V 122%nat) | 123%nat => Z_to_bv 64 (V 123%nat) | 125%nat => Z_to_bv 64 (V 125%nat) | 127%nat => Z_to_bv 64 (V 127%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 22%nat => (V 22%nat) | 23%nat => (V 23%nat) | 24%nat => (V 24%nat) | 25%nat => (V 25%nat) | 26%nat => (V 26%nat) | 27%nat => (V 27%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 40%nat => (V 40%nat) | 122%nat => (V 122%nat) | 123%nat => (V 123%nat) | 125%nat => (V 125%nat) | 127%nat => (V 127%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 128%nat. }
  assert (HR: regs_ok E PduEc.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduEc.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduEc.kn0).
  { unfold know_ok, PduEc.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | byte_tac ltac:(clear) | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV22l HV22r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV23l HV23r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV24l HV24r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV25l HV25r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV26l HV26r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV27l HV27r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K45]. }
    apply Forall_nil. }
  destruct (PduEc.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PduEc.NX0 with 140%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 2112) <= bv_unsigned a < ((V 2%nat) - 2112) + 2800) -> ~ (892864 <= bv_unsigned a < 892864 + 8) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> ~ (892888 <= bv_unsigned a < 892888 + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PduEc.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduEc.ps0) with 0xc2de8 in Hms. change (SR.ps_regs PduEc.ps0) with (map (fun i => (i, nth i PduEc.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduEc.ps0) with PduEc.cells0 in Hcells. unfold PduEc.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduEc.regs0 PduEc.regs_out0 140 KS_duEc KS_duEc_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduEc.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PduEc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV22l HV22r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV34l HV34r K6l K6r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV40l HV40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV24l HV24r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV25l HV25r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV26l HV26r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear - HV27l HV27r) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PduGc := LibSegZ_duGc.
Definition KS_duGc : list nat := Eval vm_compute in (BG.kept_list 140 PduGc.regs0 PduGc.regs_out0).
Lemma KS_duGc_ok : BG.kept_ok 140 PduGc.regs0 PduGc.regs_out0 KS_duGc = true. Proof. vm_compute. reflexivity. Qed.
Lemma duGc_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 8%nat) < 2 ^ 64 -> 0 <= (V 9%nat) < 2 ^ 64 -> 0 <= (V 18%nat) < 2 ^ 64 -> 0 <= (V 19%nat) < 2 ^ 64 -> 0 <= (V 20%nat) < 2 ^ 64 -> 0 <= (V 21%nat) < 2 ^ 64 -> 0 <= (V 22%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 118%nat) < 2 ^ 64 -> 0 <= (V 119%nat) < 2 ^ 64 -> 0 <= (V 120%nat) < 2 ^ 64 -> 0 <= (V 122%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 8) = Z_to_bv 64 0 -> getr R (reg 9) = Z_to_bv 64 892832 -> getr R (reg 18) = Z_to_bv 64 (V 118%nat) -> getr R (reg 19) = Z_to_bv 64 (V 119%nat) -> getr R (reg 20) = Z_to_bv 64 (V 120%nat) -> getr R (reg 21) = Z_to_bv 64 6491464 -> getr R (reg 22) = Z_to_bv 64 (V 122%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.defined M ((V 2%nat) - 16) 16 ->
  L5.img_clear M 65536 880640 -> 140735332552704 <= (V 33%nat) <= 140737488355311 -> 74 <= (V 34%nat) <= 131071 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + ((V 34%nat) + 1) <= ((V 2%nat) - 16)) ->
  L5.writable RSEGS M 892832 4 -> L5.writable RSEGS M 892864 8 -> L5.writable RSEGS M 892872 8 -> L5.writable RSEGS M 892888 8 ->
  L5.writable RSEGS M 892920 8 -> L5.writable RSEGS M 892928 8 -> L5.u64_at RSEGS M 892920 ((V 2%nat) + 128) -> L5.u64_at RSEGS M 892928 80 ->
  L5.u64_at RSEGS M 6491464 (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 40) (V 40%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 104) 802144 -> L5.u64_at RSEGS M ((V 2%nat) + 96) 892832 ->
  L5.u64_at RSEGS M ((V 2%nat) + 88) ((V 34%nat) + 14) -> L5.u64_at RSEGS M ((V 2%nat) + 80) 6491464 -> L5.u64_at RSEGS M ((V 2%nat) + 72) 1 -> L5.u64_at RSEGS M ((V 2%nat) + 64) 6493200 ->
  L5.u64_at RSEGS M ((V 2%nat) + 56) 0 -> L5.u64_at RSEGS M ((V 2%nat) + 48) (V 22%nat) -> L5.u32_at RSEGS M 892832 5 -> L5.u64_at RSEGS M ((V 2%nat) + 416) (V 40%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 472) 332964 -> L5.u64_at RSEGS M ((V 2%nat) + 464) 89955 -> L5.u64_at RSEGS M ((V 2%nat) + 456) 892832 -> L5.u64_at RSEGS M ((V 2%nat) + 448) ((V 2%nat) + 544) ->
  L5.u64_at RSEGS M ((V 2%nat) + 440) (V 19%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 432) (V 20%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 424) (V 21%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 536) 580508 ->
  L5.u64_at RSEGS M ((V 2%nat) + 528) (V 8%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 520) (V 9%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 512) (V 18%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 664) 773476 ->
  L5.u64_at RSEGS M ((V 2%nat) + 656) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 648) (V 42%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 640) (V 43%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 632) (V 44%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) + 624) (V 45%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 616) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 608) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 600) (V 48%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (892832 <= bv_unsigned a < 892832 + 4) -> ~ (892864 <= bv_unsigned a < 892864 + 8) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> ~ (892888 <= bv_unsigned a < 892888 + 8) -> ~ (892920 <= bv_unsigned a < 892920 + 8) -> ~ (892928 <= bv_unsigned a < 892928 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> ~ (892832 <= i < 892832 + 4) -> ~ (892864 <= i < 892864 + 8) -> ~ (892872 <= i < 892872 + 8) -> ~ (892888 <= i < 892888 + 8) -> ~ (892920 <= i < 892920 + 8) -> ~ (892928 <= i < 892928 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xc2e40 M) (st fx' R' 0xbd464 M')
        /\ (forall x, In x KS_duGc -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 773480
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 672)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 42%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 8%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 48%nat)
        /\ L5.u32_at RSEGS M' 892832 5
        /\ L5.u64_at RSEGS M' 892928 0
        /\ L5.u64_at RSEGS M' 892920 6493200
        /\ L5.u64_at RSEGS M' 892888 0
        /\ L5.u64_at RSEGS M' 892872 0
        /\ L5.u64_at RSEGS M' 892864 0).
Proof.
  intros [HV2l HV2r] [HV8l HV8r] [HV9l HV9r] [HV18l HV18r] [HV19l HV19r] [HV20l HV20r] [HV21l HV21r] [HV22l HV22r] [HV33l HV33r] [HV34l HV34r] [HV40l HV40r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV118l HV118r] [HV119l HV119r] [HV120l HV120r] [HV122l HV122r] G2 G8 G9 G18 G19 G20 G21 G22 [K0l K0r] K1 K2 K3 K4 [K5l K5r] [K6l K6r] K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 8%nat => Z_to_bv 64 (V 8%nat) | 9%nat => Z_to_bv 64 (V 9%nat) | 18%nat => Z_to_bv 64 (V 18%nat) | 19%nat => Z_to_bv 64 (V 19%nat) | 20%nat => Z_to_bv 64 (V 20%nat) | 21%nat => Z_to_bv 64 (V 21%nat) | 22%nat => Z_to_bv 64 (V 22%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 118%nat => Z_to_bv 64 (V 118%nat) | 119%nat => Z_to_bv 64 (V 119%nat) | 120%nat => Z_to_bv 64 (V 120%nat) | 122%nat => Z_to_bv 64 (V 122%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 8%nat => (V 8%nat) | 9%nat => (V 9%nat) | 18%nat => (V 18%nat) | 19%nat => (V 19%nat) | 20%nat => (V 20%nat) | 21%nat => (V 21%nat) | 22%nat => (V 22%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 118%nat => (V 118%nat) | 119%nat => (V 119%nat) | 120%nat => (V 120%nat) | 122%nat => (V 122%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 123%nat. }
  assert (HR: regs_ok E PduGc.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PduGc.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PduGc.kn0).
  { unfold know_ok, PduGc.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | exact (conj K5l K5r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K5l K5r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear; lia | clear; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r) | clear; lia | clear; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV34l HV34r K6l K6r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV22l HV22r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV40l HV40r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV19l HV19r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV20l HV20r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV21l HV21r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV8l HV8r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV9l HV9r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV18l HV18r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV42l HV42r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV43l HV43r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K7; lia | clear - HV2l HV2r K0l K0r K7; lia | exactA K47]. }
    apply Forall_nil. }
  destruct (PduGc.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PduGc.NX0 with 140%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (892832 <= bv_unsigned a < 892832 + 4) -> ~ (892864 <= bv_unsigned a < 892864 + 8) -> ~ (892872 <= bv_unsigned a < 892872 + 8) -> ~ (892888 <= bv_unsigned a < 892888 + 8) -> ~ (892920 <= bv_unsigned a < 892920 + 8) -> ~ (892928 <= bv_unsigned a < 892928 + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply Hfr. unfold PduGc.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K7) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K7 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn4; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn5; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn6; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4 Hn5 Hn6. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PduGc.ps0) with 0xbd464 in Hms. change (SR.ps_regs PduGc.ps0) with (map (fun i => (i, nth i PduGc.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PduGc.ps0) with PduGc.cells0 in Hcells. unfold PduGc.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PduGc.regs0 PduGc.regs_out0 140 KS_duGc KS_duGc_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PduGc.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PduGc.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End AS0DIAGUP.
