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
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA XIcptA XIcptAs0Kit.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegZ_ue1b1 LibSegZ_ue1e1 LibSegZ_ue1e2_bl LibSegZ_ue1e2_bh LibSegZ_ue1e3.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5ACP1.
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
Module Pue1b1 := LibSegZ_ue1b1.
Definition KS_ue1b1 : list nat := Eval vm_compute in (BG.kept_list 56 Pue1b1.regs0 Pue1b1.regs_out0).
Lemma KS_ue1b1_ok : BG.kept_ok 56 Pue1b1.regs0 Pue1b1.regs_out0 KS_ue1b1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ue1b1_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) + 32) -> getr R (reg 3) = Z_to_bv 64 67584 -> getr R (reg 4) = Z_to_bv 64 6360328 -> getr R (reg 10) = Z_to_bv 64 ((V 10%nat) - 32) ->
  140735332552704 <= (V 2%nat) <= 140737488355232 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 96 -> L5.defined M ((V 2%nat) - 64) 96 ->
  4224 <= (V 10%nat) <= 140737488355328 -> aligned (V 10%nat) 16 -> L5.writable RSEGS M ((V 10%nat) - 128) 160 -> L5.defined M ((V 10%nat) - 128) 160 ->
  (2147446784 + 17592186048512 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 160 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450864) 20 -> (((V 2%nat) - 64) + 4192 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 160 <= ((V 2%nat) - 64)) -> (((V 10%nat) - 128) + 160 <= 65536 \/ 65536 + 6434816 <= ((V 10%nat) - 128)) ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147450872) 12 -> L5.img_clear M 65536 880640 -> L5.img_clear M 892736 892768 -> L5.u64_at RSEGS M ((V 10%nat) - 32) 4849336966747728640 ->
  L5.u32_at RSEGS M ((V 10%nat) - 72) 0 -> L5.u64_at RSEGS M 6357448 0 -> L5.u32_at RSEGS M 6357456 1 -> L5.u64_at RSEGS M ((V 10%nat) - 40) (V 10%nat) ->
  L5.writable RSEGS M 6357448 8 -> L5.writable RSEGS M 6357456 4 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 96) -> ~ (((V 10%nat) - 80) <= bv_unsigned a < ((V 10%nat) - 80) + 12) -> ~ (6357448 <= bv_unsigned a < 6357448 + 8) -> ~ (6357456 <= bv_unsigned a < 6357456 + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 96) -> ~ (((V 10%nat) - 80) <= i < ((V 10%nat) - 80) + 12) -> ~ (6357448 <= i < 6357448 + 8) -> ~ (6357456 <= i < 6357456 + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e3d4 M) (st fx' R' 0x8e3d8 M')
        /\ (forall x, In x KS_ue1b1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582616
        /\ getr R' (reg 10) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ L5.u32_at RSEGS M' 6357456 0
        /\ L5.u64_at RSEGS M' 6357448 ((V 10%nat) - 128)
        /\ L5.u64_at RSEGS M' ((V 10%nat) - 80) 0
        /\ L5.u32_at RSEGS M' ((V 10%nat) - 72) 1
        /\ L5.defined M' ((V 10%nat) - 128) 48
        /\ L5.defined M' ((V 10%nat) - 68) 100).
Proof.
  intros [HV2l HV2r] [HV10l HV10r] G2 G3 G4 G10 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 10%nat => Z_to_bv 64 (V 10%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 10%nat => (V 10%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 11%nat. }
  assert (HR: regs_ok E Pue1b1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pue1b1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pue1b1.kn0).
  { unfold know_ok, Pue1b1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K21]. }
    apply Forall_nil. }
  destruct (Pue1b1.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pue1b1.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 96) -> ~ (((V 10%nat) - 80) <= bv_unsigned a < ((V 10%nat) - 80) + 12) -> ~ (6357448 <= bv_unsigned a < 6357448 + 8) -> ~ (6357456 <= bv_unsigned a < 6357456 + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold Pue1b1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pue1b1.ps0) with 0x8e3d8 in Hms. change (SR.ps_regs Pue1b1.ps0) with (map (fun i => (i, nth i Pue1b1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pue1b1.ps0) with Pue1b1.cells0 in Hcells. unfold Pue1b1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pue1b1.regs0 Pue1b1.regs_out0 56 KS_ue1b1 KS_ue1b1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pue1b1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pue1b1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1b1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pue1b1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1b1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pue1b1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1b1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pue1b1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1b1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pue1b1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1b1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pue1b1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pue1e1 := LibSegZ_ue1e1.
Definition KS_ue1e1 : list nat := Eval vm_compute in (BG.kept_list 56 Pue1e1.regs0 Pue1e1.regs_out0).
Lemma KS_ue1e1_ok : BG.kept_ok 56 Pue1e1.regs0 Pue1e1.regs_out0 KS_ue1e1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ue1e1_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) + 32) -> getr R (reg 3) = Z_to_bv 64 67584 -> getr R (reg 4) = Z_to_bv 64 6360328 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355232 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 112 -> L5.defined M ((V 2%nat) - 80) 112 ->
  4224 <= (V 10%nat) <= 140737488355328 -> aligned (V 10%nat) 16 -> L5.writable RSEGS M ((V 10%nat) - 128) 160 -> L5.defined M ((V 10%nat) - 128) 160 ->
  (2147446784 + 17592186048512 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 160 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450864) 20 -> 4096 <= (V 37%nat) <= 140737488355328 -> aligned (V 37%nat) 16 ->
  L5.writable RSEGS M (V 37%nat) 41 -> L5.defined M (V 37%nat) 41 -> (((V 2%nat) - 80) + 4208 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 160 <= ((V 2%nat) - 80)) -> (((V 10%nat) - 128) + 160 <= (V 37%nat) \/ (V 37%nat) + 41 <= ((V 10%nat) - 128)) ->
  (((V 2%nat) - 80) + 4208 <= (V 37%nat) \/ (V 37%nat) + 41 <= ((V 2%nat) - 80)) -> (((V 10%nat) - 128) + 160 <= 65536 \/ 65536 + 6434816 <= ((V 10%nat) - 128)) -> ((V 37%nat) + 41 <= 65536 \/ 65536 + 6434816 <= (V 37%nat)) -> L5KA.zeros_at M (((V 2%nat) / 8) + 2147450870) 14 ->
  L5.img_clear M 65536 880640 -> L5.img_clear M 892736 892768 -> L5.u64_at RSEGS M 6357448 ((V 10%nat) - 128) -> L5.u64_at RSEGS M ((V 10%nat) - 32) 4849336966747728640 ->
  L5.u32_at RSEGS M ((V 10%nat) - 72) 1 -> L5.u64_at RSEGS M ((V 10%nat) - 80) 0 -> L5.u64_at RSEGS M ((V 10%nat) - 120) 1 -> L5.u64_at RSEGS M ((V 10%nat) - 104) 731988 ->
  L5.u64_at RSEGS M ((V 10%nat) + 8) ((V 37%nat) + 24) -> L5.u32_at RSEGS M ((V 37%nat) + 16) 0 -> L5.writable RSEGS M 6357448 8 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 112) -> ~ (((V 10%nat) - 120) <= bv_unsigned a < ((V 10%nat) - 120) + 128) -> ~ (((V 37%nat) + 16) <= bv_unsigned a < ((V 37%nat) + 16) + 4) -> ~ (6357448 <= bv_unsigned a < 6357448 + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 112) -> ~ (((V 10%nat) - 120) <= i < ((V 10%nat) - 120) + 128) -> ~ (((V 37%nat) + 16) <= i < ((V 37%nat) + 16) + 4) -> ~ (6357448 <= i < 6357448 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x8e3d8 M) (st fx' R' 0x5fc54 M')
        /\ (forall x, In x KS_ue1e1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 718792
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 16)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 10%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 18446744073709551615
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551615
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) ((V 10%nat) - 128)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) 722996
        /\ L5.u32_at RSEGS M' ((V 37%nat) + 16) 18446744073709551615
        /\ L5.u64_at RSEGS M' (V 10%nat) 873376
        /\ L5.u64_at RSEGS M' ((V 10%nat) - 120) 0
        /\ L5.u64_at RSEGS M' 6357448 0
        /\ L5.u32_at RSEGS M' ((V 10%nat) - 72) 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 8) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) + 24) 582620
        /\ L5.defined M' (V 2%nat) 8
        /\ L5.defined M' ((V 10%nat) - 128) 8
        /\ L5.defined M' ((V 10%nat) - 112) 40
        /\ L5.defined M' ((V 10%nat) - 68) 68
        /\ L5.defined M' ((V 10%nat) + 8) 24
        /\ L5.defined M' (V 37%nat) 16
        /\ L5.defined M' ((V 37%nat) + 20) 21
        /\ L5.u64_at RSEGS M' ((V 10%nat) - 32) 4849336966747728640
        /\ L5.u64_at RSEGS M' ((V 10%nat) - 80) 0
        /\ L5.u64_at RSEGS M' ((V 10%nat) - 104) 731988).
Proof.
  intros [HV2l HV2r] [HV10l HV10r] [HV37l HV37r] [HV40l HV40r] G2 G3 G4 G10 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 K8 K9 [K10l K10r] K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 K25 K26 K27 K28 K29 K30.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 10%nat => Z_to_bv 64 (V 10%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 10%nat => (V 10%nat) | 37%nat => (V 37%nat) | 40%nat => (V 40%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E Pue1e1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pue1e1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pue1e1.kn0).
  { unfold know_ok, Pue1e1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K16; lia | clear - HV2l HV2r K0l K0r K14 K16; lia | clear - HV2l HV2r K0l K0r K14 K16; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K16; lia | clear - HV2l HV2r K0l K0r K14 K16; lia | clear - HV2l HV2r K0l K0r K14 K16; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | exact (conj K10l K10r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | clear; lia | exact K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K10l K10r K15 K16 K18; lia | clear - HV37l HV37r K10l K10r K15 K16 K18; lia | clear - HV37l HV37r K10l K10r K15 K16 K18; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K10l K10r K15 K16 K18; lia | clear - HV37l HV37r K10l K10r K15 K16 K18; lia | clear - HV37l HV37r K10l K10r K15 K16 K18; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K16; lia | clear - HV2l HV2r K0l K0r K14 K16; lia | clear - HV2l HV2r K0l K0r K14 K16; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | clear; lia | clear; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | clear - HV10l HV10r K4l K4r K8 K14 K15 K17; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk ZA ltac:(clear) | clear - HV37l HV37r K10l K10r K15 K16 K18; lia | clear - HV37l HV37r K10l K10r K15 K16 K18; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K30]. }
    apply Forall_nil. }
  destruct (Pue1e1.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pue1e1.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 112) -> ~ (((V 10%nat) - 120) <= bv_unsigned a < ((V 10%nat) - 120) + 128) -> ~ (((V 37%nat) + 16) <= bv_unsigned a < ((V 37%nat) + 16) + 4) -> ~ (6357448 <= bv_unsigned a < 6357448 + 8) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold Pue1e1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K14 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K14 K15 K17 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear - HV37l HV37r K10l K10r K15 K16 K18 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear - Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pue1e1.ps0) with 0x5fc54 in Hms. change (SR.ps_regs Pue1e1.ps0) with (map (fun i => (i, nth i Pue1e1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pue1e1.ps0) with Pue1e1.cells0 in Hcells. unfold Pue1e1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pue1e1.regs0 Pue1e1.regs_out0 56 KS_ue1e1 KS_ue1e1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pue1e1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pue1e1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pue1e1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pue1e1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pue1e1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pue1e1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pue1e1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth Pue1e1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K14 K16) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV37l HV37r K10l K10r K15 K16 K18) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K4l K4r K8 K14 K15 K17) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pue1e2_bl := LibSegZ_ue1e2_bl.
Definition KS_ue1e2_bl : list nat := Eval vm_compute in (BG.kept_list 56 Pue1e2_bl.regs0 Pue1e2_bl.regs_out0).
Lemma KS_ue1e2_bl_ok : BG.kept_ok 56 Pue1e2_bl.regs0 Pue1e2_bl.regs_out0 KS_ue1e2_bl = true. Proof. vm_compute. reflexivity. Qed.
Lemma ue1e2_bl_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 3) = Z_to_bv 64 67584 -> getr R (reg 4) = Z_to_bv 64 6360328 -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 64 -> L5.defined M ((V 2%nat) - 80) 64 ->
  4224 <= (V 10%nat) <= 65504 -> aligned (V 10%nat) 16 -> L5.writable RSEGS M ((V 10%nat) - 128) 160 -> L5.defined M ((V 10%nat) - 128) 160 ->
  (2147446784 + 17592186048512 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 160 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450864) 20 -> (((V 2%nat) - 80) + 4160 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 160 <= ((V 2%nat) - 80)) -> (((V 10%nat) - 128) + 160 <= 65536 \/ 65536 + 6434816 <= ((V 10%nat) - 128)) ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147450870) 8 -> L5.img_clear M 65536 880640 -> L5.img_clear M 892736 892768 -> L5.u64_at RSEGS M ((V 2%nat) - 8) 722996 ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) ((V 10%nat) - 128) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf7c8 M) (st fx' R' 0x5fc54 M')
        /\ (forall x, In x KS_ue1e2_bl -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 723004
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 10%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 10%nat) - 128)
        /\ getr R' (reg 11) = Z_to_bv 64 6357472
        /\ getr R' (reg 12) = Z_to_bv 64 6357488).
Proof.
  intros [HV2l HV2r] [HV10l HV10r] [HV40l HV40r] G2 G3 G4 G8 G10 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 10%nat => Z_to_bv 64 (V 10%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 10%nat => (V 10%nat) | 40%nat => (V 40%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E Pue1e2_bl.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pue1e2_bl.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pue1e2_bl.kn0).
  { unfold know_ok, Pue1e2_bl.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K16]. }
    apply Forall_nil. }
  destruct (Pue1e2_bl.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pue1e2_bl.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 64) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pue1e2_bl.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pue1e2_bl.ps0) with 0x5fc54 in Hms. change (SR.ps_regs Pue1e2_bl.ps0) with (map (fun i => (i, nth i Pue1e2_bl.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pue1e2_bl.ps0) with Pue1e2_bl.cells0 in Hcells. unfold Pue1e2_bl.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pue1e2_bl.regs0 Pue1e2_bl.regs_out0 56 KS_ue1e2_bl KS_ue1e2_bl_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pue1e2_bl.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pue1e2_bl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e2_bl.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pue1e2_bl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e2_bl.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pue1e2_bl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e2_bl.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pue1e2_bl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e2_bl.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pue1e2_bl.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pue1e2_bl.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pue1e2_bl.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pue1e2_bh := LibSegZ_ue1e2_bh.
Definition KS_ue1e2_bh : list nat := Eval vm_compute in (BG.kept_list 56 Pue1e2_bh.regs0 Pue1e2_bh.regs_out0).
Lemma KS_ue1e2_bh_ok : BG.kept_ok 56 Pue1e2_bh.regs0 Pue1e2_bh.regs_out0 KS_ue1e2_bh = true. Proof. vm_compute. reflexivity. Qed.
Lemma ue1e2_bh_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 16) -> getr R (reg 3) = Z_to_bv 64 67584 -> getr R (reg 4) = Z_to_bv 64 6360328 -> getr R (reg 8) = Z_to_bv 64 (V 10%nat) -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 80) 64 -> L5.defined M ((V 2%nat) - 80) 64 ->
  6500480 <= (V 10%nat) <= 140737488355328 -> aligned (V 10%nat) 16 -> L5.writable RSEGS M ((V 10%nat) - 128) 160 -> L5.defined M ((V 10%nat) - 128) 160 ->
  (2147446784 + 17592186048512 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 160 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450864) 20 -> (((V 2%nat) - 80) + 4160 <= ((V 10%nat) - 128) \/ ((V 10%nat) - 128) + 160 <= ((V 2%nat) - 80)) -> (((V 10%nat) - 128) + 160 <= 65536 \/ 65536 + 6434816 <= ((V 10%nat) - 128)) ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147450870) 8 -> L5.img_clear M 65536 880640 -> L5.img_clear M 892736 892768 -> L5.u64_at RSEGS M ((V 2%nat) - 8) 722996 ->
  L5.u64_at RSEGS M ((V 2%nat) - 16) ((V 10%nat) - 128) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 80) <= i < ((V 2%nat) - 80) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xaf7c8 M) (st fx' R' 0x5fc54 M')
        /\ (forall x, In x KS_ue1e2_bh -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 723004
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 ((V 10%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 10%nat) - 128)
        /\ getr R' (reg 11) = Z_to_bv 64 6357472
        /\ getr R' (reg 12) = Z_to_bv 64 6357488
        /\ getr R' (reg 14) = Z_to_bv 64 6358000).
Proof.
  intros [HV2l HV2r] [HV10l HV10r] [HV40l HV40r] G2 G3 G4 G8 G10 [K0l K0r] K1 K2 K3 [K4l K4r] K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 10%nat => Z_to_bv 64 (V 10%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 10%nat => (V 10%nat) | 40%nat => (V 40%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 41%nat. }
  assert (HR: regs_ok E Pue1e2_bh.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pue1e2_bh.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pue1e2_bh.kn0).
  { unfold know_ok, Pue1e2_bh.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K3]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | exact (conj K4l K4r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | clear - HV10l HV10r K4l K4r K8 K10 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk ZA ltac:(clear - HV10l HV10r K4l K4r K8 K10 K11) | clear - HV2l HV2r K0l K0r K10; lia | clear - HV2l HV2r K0l K0r K10; lia | exactA K16]. }
    apply Forall_nil. }
  destruct (Pue1e2_bh.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pue1e2_bh.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 80) <= bv_unsigned a < ((V 2%nat) - 80) + 64) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pue1e2_bh.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K10) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K10 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pue1e2_bh.ps0) with 0x5fc54 in Hms. change (SR.ps_regs Pue1e2_bh.ps0) with (map (fun i => (i, nth i Pue1e2_bh.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pue1e2_bh.ps0) with Pue1e2_bh.cells0 in Hcells. unfold Pue1e2_bh.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pue1e2_bh.regs0 Pue1e2_bh.regs_out0 56 KS_ue1e2_bh KS_ue1e2_bh_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pue1e2_bh.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pue1e2_bh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e2_bh.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pue1e2_bh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e2_bh.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pue1e2_bh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e2_bh.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth Pue1e2_bh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e2_bh.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth Pue1e2_bh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e2_bh.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth Pue1e2_bh.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pue1e2_bh.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth Pue1e2_bh.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module Pue1e3 := LibSegZ_ue1e3.
Definition KS_ue1e3 : list nat := Eval vm_compute in (BG.kept_list 56 Pue1e3.regs0 Pue1e3.regs_out0).
Lemma KS_ue1e3_ok : BG.kept_ok 56 Pue1e3.regs0 Pue1e3.regs_out0 KS_ue1e3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma ue1e3_conc (HFILL : XIAS0.fill_spec) (HCOPY : XIAS0.copy_spec) (HTLS : XIAS0.tls_spec) fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 3) = Z_to_bv 64 67584 -> getr R (reg 4) = Z_to_bv 64 6360328 -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) ->
  140735332552704 <= (V 2%nat) <= 140737488355264 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.defined M ((V 2%nat) - 64) 64 ->
  L5KA.zeros_at M (((V 2%nat) / 8) + 2147450872) 8 -> L5.img_clear M 65536 880640 -> L5.img_clear M 892736 892768 -> L5.u64_at RSEGS M ((V 2%nat) + 24) 582620 ->
  L5.u64_at RSEGS M ((V 2%nat) + 16) (V 41%nat) -> L5.u64_at RSEGS M ((V 2%nat) + 8) ((V 2%nat) + 32) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb083c M) (st fx' R' 0x8e3dc M')
        /\ (forall x, In x KS_ue1e3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 582620
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) + 32)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) + 32)).
Proof.
  intros [HV2l HV2r] [HV40l HV40r] [HV41l HV41r] G2 G3 G4 G10 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E Pue1e3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl Pue1e3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M Pue1e3.kn0).
  { unfold know_ok, Pue1e3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K3]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K5]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV41l HV41r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K9]. }
    apply Forall_nil. }
  destruct (Pue1e3.seg_sound_ax HFILL HCOPY HTLS fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change Pue1e3.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold Pue1e3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc Pue1e3.ps0) with 0x8e3dc in Hms. change (SR.ps_regs Pue1e3.ps0) with (map (fun i => (i, nth i Pue1e3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells Pue1e3.ps0) with Pue1e3.cells0 in Hcells. unfold Pue1e3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' Pue1e3.regs0 Pue1e3.regs_out0 56 KS_ue1e3 KS_ue1e3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg Pue1e3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth Pue1e3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e3.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth Pue1e3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg Pue1e3.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth Pue1e3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg Pue1e3.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth Pue1e3.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End L5ACP1.
