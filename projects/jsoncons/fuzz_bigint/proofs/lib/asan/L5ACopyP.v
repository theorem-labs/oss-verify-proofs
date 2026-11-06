(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegZ_cpI LibSegZ_cpD LibSegZ_cpaI LibSegZ_cpaD LibSegZ_acA LibSegZ_acB LibSegZ_acC LibSegZ_acD.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5ACPYP.
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
Local Ltac zfacts :=
  repeat (match goal with |- context [Z.land ?a ?m] =>
    lazymatch goal with _ : 0 <= Z.land a m <= m |- _ => fail | _ => pose proof (L5K.land_le_r a m ltac:(lia) ltac:(lia)) end end);
  repeat (match goal with |- context [?a / ?c] =>
    lazymatch goal with _ : 0 <= a / c |- _ => fail | _ => pose proof (Z.div_pos a c ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le a c ltac:(lia)) end end).
Local Ltac nonneg_tac := first [lia | match goal with |- 0 <= ?x mod ?m => exact (proj1 (Z.mod_pos_bound x m ltac:(clear; lia))) end | (zfacts; lia)].
Local Ltac byte_go :=
  lazymatch goal with
  | |- 0 <= Z.lor _ _ < 256 => apply lor_byte; byte_go
  | |- 0 <= Z.land _ _ < 256 => apply land_byte; [nonneg_tac | lia]
  | _ => zfacts; first [lia | rewrite !Z.mod_small by (rewrite ?Z.mod_small by lia; lia); lia]
  end.
Local Ltac byte_tac0 k := k; byte_go.
Tactic Notation "byte_tac" tactic(k) := byte_tac0 k.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac solve_modk k :=
  repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; lia) end;
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
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by lia end; f_equal; clear; lia]) ].
(* [comment removed for export] *)
Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by lia end; f_equal; clear; lia ].
(* [comment removed for export] *)
Module PcpI := LibSegZ_cpI.
Definition KS_cpI : list nat := Eval vm_compute in (BG.kept_list 56 PcpI.regs0 PcpI.regs_out0).
Lemma KS_cpI_ok : BG.kept_ok 56 PcpI.regs0 PcpI.regs_out0 KS_cpI = true. Proof. vm_compute. reflexivity. Qed.
Lemma cpI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 16)) ->
  4096 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 4 ->
  (((V 2%nat) - 16) + 16 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 16)) -> ((V 33%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 33%nat)) -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 ->
  L5.u8_at RSEGS M (V 34%nat) (V 36%nat) -> 0 <= (V 36%nat) <= 255 -> L5.u64_at RSEGS M ((V 34%nat) + 8) (V 37%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 34%nat) + 24) (V 39%nat) -> Z.testbit (V 36%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x917fc M) (st fx' R' 0x918fc M')
        /\ (forall x, In x KS_cpI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 2147450880
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 24) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (V 37%nat)
        /\ L5.u8_at RSEGS M' (V 33%nat) ((((4 * ((V 35%nat) / 4)) mod 2 ^ 64) + (Z.land (V 36%nat) 2)) mod 2 ^ 64)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 K14 K15 K16 K17 K18 [K19l K19r] K20 [K21l K21r] K22 K23 K24 K25.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PcpI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PcpI.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PcpI.kn0).
  { unfold know_ok, PcpI.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K16; lia | clear - HV2l HV2r K0l K0r K11 K16; lia | clear - HV2l HV2r K0l K0r K11 K16; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear - HV35l HV35r K19l K19r) | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | byte_tac ltac:(clear - HV35l HV35r K19l K19r) | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K25) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | byte_tac ltac:(clear - HV36l HV36r K21l K21r K25) | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K25) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K25) | clear; lia | rewrite (L5K.land1_bit0_false (V 36%nat) ltac:(clear - HV36l HV36r K21l K21r K25; lia) K25); clear; lia]. }
    apply Forall_nil. }
  destruct (PcpI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PcpI.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PcpI.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K17 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PcpI.ps0) with 0x918fc in Hms. change (SR.ps_regs PcpI.ps0) with (map (fun i => (i, nth i PcpI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PcpI.ps0) with PcpI.cells0 in Hcells. unfold PcpI.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PcpI.regs0 PcpI.regs_out0 56 KS_cpI KS_cpI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PcpI.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PcpI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PcpI.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PcpI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PcpI.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PcpI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PcpI.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PcpI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PcpI.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PcpI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PcpI.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PcpI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV35l HV35r K19l K19r HV36l HV36r K21l K21r K25) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PcpD := LibSegZ_cpD.
Definition KS_cpD : list nat := Eval vm_compute in (BG.kept_list 56 PcpD.regs0 PcpD.regs_out0).
Lemma KS_cpD_ok : BG.kept_ok 56 PcpD.regs0 PcpD.regs_out0 KS_cpD = true. Proof. vm_compute. reflexivity. Qed.
Lemma cpD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 16)) ->
  4096 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 4 ->
  (((V 2%nat) - 16) + 16 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 16)) -> ((V 33%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 33%nat)) -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 ->
  L5.u8_at RSEGS M (V 34%nat) (V 36%nat) -> 0 <= (V 36%nat) <= 255 -> L5.u64_at RSEGS M ((V 34%nat) + 8) (V 37%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 34%nat) + 24) (V 39%nat) -> Z.testbit (V 36%nat) 0 = true ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x917fc M) (st fx' R' 0x91968 M')
        /\ (forall x, In x KS_cpD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 1
        /\ getr R' (reg 14) = Z_to_bv 64 2147450880).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 K14 K15 K16 K17 K18 [K19l K19r] K20 [K21l K21r] K22 K23 K24 K25.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PcpD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PcpD.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PcpD.kn0).
  { unfold know_ok, PcpD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K16; lia | clear - HV2l HV2r K0l K0r K11 K16; lia | clear - HV2l HV2r K0l K0r K11 K16; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear - HV35l HV35r K19l K19r) | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | byte_tac ltac:(clear - HV35l HV35r K19l K19r) | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K25) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | byte_tac ltac:(clear - HV36l HV36r K21l K21r K25) | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K25) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K25) | clear; lia | rewrite (L5K.land1_bit0_true (V 36%nat) ltac:(clear - HV36l HV36r K21l K21r K25; lia) K25); clear; lia]. }
    apply Forall_nil. }
  destruct (PcpD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PcpD.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PcpD.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K16 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PcpD.ps0) with 0x91968 in Hms. change (SR.ps_regs PcpD.ps0) with (map (fun i => (i, nth i PcpD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PcpD.ps0) with PcpD.cells0 in Hcells. unfold PcpD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PcpD.regs0 PcpD.regs_out0 56 KS_cpD KS_cpD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PcpD.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PcpD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PcpD.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PcpD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PcpD.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PcpD.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PcpaI := LibSegZ_cpaI.
Definition KS_cpaI : list nat := Eval vm_compute in (BG.kept_list 56 PcpaI.regs0 PcpaI.regs_out0).
Lemma KS_cpaI_ok : BG.kept_ok 56 PcpaI.regs0 PcpaI.regs_out0 KS_cpaI = true. Proof. vm_compute. reflexivity. Qed.
Lemma cpaI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 16)) ->
  4096 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 4 ->
  (((V 2%nat) - 16) + 16 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 16)) -> ((V 33%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 33%nat)) -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 ->
  L5.u8_at RSEGS M (V 34%nat) (V 36%nat) -> 0 <= (V 36%nat) <= 255 -> L5.u64_at RSEGS M ((V 34%nat) + 8) (V 37%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 34%nat) + 24) (V 39%nat) -> Z.testbit (V 36%nat) 0 = false ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 32) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 32) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x938e8 M) (st fx' R' 0x939e8 M')
        /\ (forall x, In x KS_cpaI -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 14) = Z_to_bv 64 2147450880
        /\ getr R' (reg 15) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 24) (V 39%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (V 37%nat)
        /\ L5.u8_at RSEGS M' (V 33%nat) ((((4 * ((V 35%nat) / 4)) mod 2 ^ 64) + (Z.land (V 36%nat) 2)) mod 2 ^ 64)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 K14 K15 K16 K17 K18 [K19l K19r] K20 [K21l K21r] K22 K23 K24 K25.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PcpaI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PcpaI.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PcpaI.kn0).
  { unfold know_ok, PcpaI.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K16; lia | clear - HV2l HV2r K0l K0r K11 K16; lia | clear - HV2l HV2r K0l K0r K11 K16; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear - HV35l HV35r K19l K19r) | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | byte_tac ltac:(clear - HV35l HV35r K19l K19r) | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K25) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | byte_tac ltac:(clear - HV36l HV36r K21l K21r K25) | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K25) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K25) | clear; lia | rewrite (L5K.land1_bit0_false (V 36%nat) ltac:(clear - HV36l HV36r K21l K21r K25; lia) K25); clear; lia]. }
    apply Forall_nil. }
  destruct (PcpaI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PcpaI.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 32) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PcpaI.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K16 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K17 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PcpaI.ps0) with 0x939e8 in Hms. change (SR.ps_regs PcpaI.ps0) with (map (fun i => (i, nth i PcpaI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PcpaI.ps0) with PcpaI.cells0 in Hcells. unfold PcpaI.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PcpaI.regs0 PcpaI.regs_out0 56 KS_cpaI KS_cpaI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PcpaI.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PcpaI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PcpaI.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PcpaI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PcpaI.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PcpaI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PcpaI.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PcpaI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PcpaI.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PcpaI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PcpaI.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PcpaI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk' ZA Hag ltac:(clear - HV39l HV39r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk' ZA Hag ltac:(clear - HV38l HV38r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia]. }
  eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV35l HV35r K19l K19r HV36l HV36r K21l K21r K25) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PcpaD := LibSegZ_cpaD.
Definition KS_cpaD : list nat := Eval vm_compute in (BG.kept_list 56 PcpaD.regs0 PcpaD.regs_out0).
Lemma KS_cpaD_ok : BG.kept_ok 56 PcpaD.regs0 PcpaD.regs_out0 KS_cpaD = true. Proof. vm_compute. reflexivity. Qed.
Lemma cpaD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332487184 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 16) 16 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 16) + 16 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 16)) ->
  4096 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 4 ->
  (((V 2%nat) - 16) + 16 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 16)) -> ((V 33%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 33%nat)) -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 ->
  L5.u8_at RSEGS M (V 34%nat) (V 36%nat) -> 0 <= (V 36%nat) <= 255 -> L5.u64_at RSEGS M ((V 34%nat) + 8) (V 37%nat) -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 38%nat) ->
  L5.u64_at RSEGS M ((V 34%nat) + 24) (V 39%nat) -> Z.testbit (V 36%nat) 0 = true ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 16) <= i < ((V 2%nat) - 16) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x938e8 M) (st fx' R' 0x91968 M')
        /\ (forall x, In x KS_cpaD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 13) = Z_to_bv 64 (((V 34%nat) / 8) + 2147450880)
        /\ getr R' (reg 14) = Z_to_bv 64 2147450880
        /\ getr R' (reg 15) = Z_to_bv 64 1).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 K14 K15 K16 K17 K18 [K19l K19r] K20 [K21l K21r] K22 K23 K24 K25.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 40%nat. }
  assert (HR: regs_ok E PcpaD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PcpaD.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PcpaD.kn0).
  { unfold know_ok, PcpaD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K16; lia | clear - HV2l HV2r K0l K0r K11 K16; lia | clear - HV2l HV2r K0l K0r K11 K16; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17) | evalEk ZA ltac:(clear - HV35l HV35r K19l K19r) | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | clear - HV33l HV33r K6l K6r K8 K11 K17; lia | byte_tac ltac:(clear - HV35l HV35r K19l K19r) | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K25) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | byte_tac ltac:(clear - HV36l HV36r K21l K21r K25) | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K25) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV37l HV37r) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV38l HV38r) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17) | evalEk ZA ltac:(clear - HV39l HV39r) | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | clear - HV34l HV34r K12l K12r K14 K16 K17; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K25) | clear; lia | rewrite (L5K.land1_bit0_true (V 36%nat) ltac:(clear - HV36l HV36r K21l K21r K25; lia) K25); clear; lia]. }
    apply Forall_nil. }
  destruct (PcpaD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PcpaD.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 16) <= bv_unsigned a < ((V 2%nat) - 16) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PcpaD.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11 K16) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K16 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PcpaD.ps0) with 0x91968 in Hms. change (SR.ps_regs PcpaD.ps0) with (map (fun i => (i, nth i PcpaD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PcpaD.ps0) with PcpaD.cells0 in Hcells. unfold PcpaD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PcpaD.regs0 PcpaD.regs_out0 56 KS_cpaD KS_cpaD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PcpaD.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PcpaD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PcpaD.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PcpaD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PcpaD.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PcpaD.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PacA := LibSegZ_acA.
Definition KS_acA : list nat := Eval vm_compute in (BG.kept_list 56 PacA.regs0 PacA.regs_out0).
Lemma KS_acA_ok : BG.kept_ok 56 PacA.regs0 PacA.regs_out0 KS_acA = true. Proof. vm_compute. reflexivity. Qed.
Lemma acA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 34%nat) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x91968 M) (st fx' R' 0x489b8 M')
        /\ (forall x, In x KS_acA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 596440
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 96
        /\ getr R' (reg 11) = Z_to_bv 64 908088
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 2147450880
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 128) 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PacA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PacA.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PacA.kn0).
  { unfold know_ok, PacA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_nil. }
  destruct (PacA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PacA.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PacA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PacA.ps0) with 0x489b8 in Hms. change (SR.ps_regs PacA.ps0) with (map (fun i => (i, nth i PacA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PacA.ps0) with PacA.cells0 in Hcells. unfold PacA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PacA.regs0 PacA.regs_out0 56 KS_acA KS_acA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PacA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PacA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PacA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PacA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PacA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PacA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PacA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PacA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PacA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PacA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacA.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PacA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PacB := LibSegZ_acB.
Definition KS_acB : list nat := Eval vm_compute in (BG.kept_list 56 PacB.regs0 PacB.regs_out0).
Lemma KS_acB_ok : BG.kept_ok 56 PacB.regs0 PacB.regs_out0 KS_acB = true. Proof. vm_compute. reflexivity. Qed.
Lemma acB_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 (V 33%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 40%nat) <= 140737488355200 -> aligned (V 40%nat) 32 ->
  L5.defined M (V 40%nat) 128 -> L5.writable RSEGS M (V 40%nat) 128 -> (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 40%nat) + 120) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 -> L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) ->
  ((V 40%nat) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 128) + 128 <= (V 40%nat) \/ (V 40%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 128 <= (V 33%nat)) ->
  ((V 33%nat) + 32 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) -> ((V 34%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 128 <= (V 34%nat)) -> ((V 34%nat) + 32 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 34%nat)) ->
  ((((V 34%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 16 <= (((V 34%nat) / 8) + 2147450880)) -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 -> (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) ->
  L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) -> 4096 <= (V 34%nat) <= 140737488355296 ->
  aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 4 -> (((V 2%nat) - 128) + 128 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 128)) ->
  ((V 33%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 33%nat)) -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 -> L5.u8_at RSEGS M (V 34%nat) (V 36%nat) ->
  0 <= (V 36%nat) <= 255 -> Z.testbit (V 36%nat) 0 = true -> L5.u64_at RSEGS M ((V 34%nat) + 8) (V 37%nat) -> 0 <= (V 37%nat) <= 16777216 ->
  L5.u64_at RSEGS M ((V 34%nat) + 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 39%nat) -> 4096 <= (V 39%nat) <= 140737488355328 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 8) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 32) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 12) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 104) <= i < ((V 2%nat) - 104) + 8) -> ~ (((V 33%nat) + 0) <= i < ((V 33%nat) + 0) + 32) -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 24) -> ~ ((((V 40%nat) / 8) + 2147450880) <= i < (((V 40%nat) / 8) + 2147450880) + 12) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x919d8 M) (st fx' R' 0xd0fe0 M')
        /\ (forall x, In x KS_acB -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 596796
        /\ getr R' (reg 10) = Z_to_bv 64 (8 * (V 38%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551608
        /\ getr R' (reg 18) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 33%nat) + 24) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 34%nat) + 8)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 40%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((((V 34%nat) + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 24) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 16) (V 38%nat)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 8) (V 37%nat)
        /\ L5.u8_at RSEGS M' (V 33%nat) (Z.lor (Z.land (V 36%nat) 2) (Z.land ((((2 * ((V 35%nat) / 2)) mod 2 ^ 64) + 1) mod 2 ^ 64) 253))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (V 40%nat)
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450888) 243
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 16) 596328
        /\ L5.u64_at RSEGS M' ((V 40%nat) + 8) 127756
        /\ L5.u64_at RSEGS M' (V 40%nat) 1102416563
        /\ L5.defined M' ((V 40%nat) + 24) 104).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] [HV41l HV41r] [HV43l HV43r] G1 G2 G8 G9 G10 G19 G20 G25 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r] K14 K15 K16 K17 K18 K19 K20 K21 K22 K23 K24 [K25l K25r] K26 K27 K28 K29 K30 [K31l K31r] K32 K33 K34 K35 K36 K37 [K38l K38r] K39 [K40l K40r] K41 K42 [K43l K43r] K44 [K45l K45r] K46 [K47l K47r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 43%nat => (V 43%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PacB.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PacB.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PacB.kn0).
  { unfold know_ok, PacB.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K30 K35) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K30 K35) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K30 K35) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K30 K35; lia | clear - HV2l HV2r K0l K0r K17 K18 K30 K35; lia | clear - HV2l HV2r K0l K0r K17 K18 K30 K35; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20 K23) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24; lia | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20 K23) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20 K23) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K13l K13r K15 K16 K18 K20 K23; lia | clear - HV41l HV41r K13l K13r K15 K16 K18 K20 K23; lia | clear - HV41l HV41r K13l K13r K15 K16 K18 K20 K23; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20 K23) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20 K23) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K30 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K30 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20 K23) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20 K23) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K13l K13r K15 K16 K18 K20 K23) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | clear; lia | exact K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36; lia | clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36; lia | clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36; lia | clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36; lia | clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K30 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36) | exact (conj K31l K31r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36) | clear; lia | exact K32]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36; lia | clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36; lia | clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K17 K18 K30 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | evalEk ZA ltac:(clear - HV35l HV35r K38l K38r) | clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36; lia | clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36; lia | byte_tac ltac:(clear - HV35l HV35r K38l K38r) | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K38l K38r) | exact (conj K38l K38r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36) | evalEk ZA ltac:(clear - HV36l HV36r K40l K40r K41) | clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36; lia | clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36; lia | byte_tac ltac:(clear - HV36l HV36r K40l K40r K41) | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K40l K40r K41) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV36l HV36r K40l K40r K41) | clear; lia | rewrite (L5K.land1_bit0_true (V 36%nat) ltac:(clear - HV36l HV36r K40l K40r K41; lia) K41); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36) | evalEk ZA ltac:(clear - HV37l HV37r K43l K43r) | clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36; lia | clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K43l K43r) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36) | evalEk ZA ltac:(clear - HV38l HV38r K45l K45r) | clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36; lia | clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K45l K45r) | exact (conj K45l K45r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36) | evalEk ZA ltac:(clear - HV39l HV39r K47l K47r) | clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36; lia | clear - HV34l HV34r K22 K23 K24 K31l K31r K33 K35 K36; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K47l K47r) | exact (conj K47l K47r)]. }
    apply Forall_nil. }
  destruct (PacB.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PacB.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 104) <= bv_unsigned a < ((V 2%nat) - 104) + 8) -> ~ (((V 33%nat) + 0) <= bv_unsigned a < ((V 33%nat) + 0) + 32) -> ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 24) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 12) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PacB.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K30 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K17 K18 K30 K35 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24 Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PacB.ps0) with 0xd0fe0 in Hms. change (SR.ps_regs PacB.ps0) with (map (fun i => (i, nth i PacB.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PacB.ps0) with PacB.cells0 in Hcells. unfold PacB.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PacB.regs0 PacB.regs_out0 56 KS_acB KS_acB_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PacB.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PacB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacB.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PacB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacB.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PacB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacB.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PacB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacB.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PacB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacB.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PacB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacB.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PacB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacB.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PacB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacB.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PacB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacB.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PacB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacB.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PacB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacB.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PacB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacB.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PacB.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K45l K45r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K43l K43r) | clear; lia]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K19 K20 K21 K25l K25r K27 K30 K36) | (L5K.evalB' ZA Hag; den_tac) | byte_tac ltac:(clear - HV35l HV35r K38l K38r HV36l HV36r K40l K40r K41) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K17 K18 K30 K35) | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 20%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K6l K6r K10 K16 K17 K19 K21 K22 K24) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PacC := LibSegZ_acC.
Definition KS_acC : list nat := Eval vm_compute in (BG.kept_list 56 PacC.regs0 PacC.regs_out0).
Lemma KS_acC_ok : BG.kept_ok 56 PacC.regs0 PacC.regs_out0 KS_acC = true. Proof. vm_compute. reflexivity. Qed.
Lemma acC_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 42%nat) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 19) = Z_to_bv 64 (V 34%nat) -> getr R (reg 20) = Z_to_bv 64 ((((V 33%nat) + 24) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 34%nat) + 8) -> getr R (reg 22) = Z_to_bv 64 ((V 33%nat) + 24) -> getr R (reg 23) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 ((((V 34%nat) + 8) / 8) + 2147450880) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 128) + 128 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 128)) ->
  4096 <= (V 34%nat) <= 140737488355296 -> aligned (V 34%nat) 8 -> (2147446784 + 17592186048512 <= (V 34%nat) \/ (V 34%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 34%nat) / 8) + 2147450880) 4 ->
  (((V 2%nat) - 128) + 128 <= (V 34%nat) \/ (V 34%nat) + 32 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 32 <= (V 34%nat) \/ (V 34%nat) + 32 <= (V 33%nat)) -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 ->
  L5.u8_at RSEGS M (V 34%nat) (V 36%nat) -> 0 <= (V 36%nat) <= 255 -> Z.testbit (V 36%nat) 0 = true -> L5.u64_at RSEGS M ((V 34%nat) + 8) (V 37%nat) ->
  0 <= (V 37%nat) <= 16777216 -> L5.u64_at RSEGS M ((V 34%nat) + 16) (V 38%nat) -> 0 <= (V 38%nat) <= 16777216 -> L5.u64_at RSEGS M ((V 34%nat) + 24) (V 39%nat) ->
  4096 <= (V 39%nat) <= 140737488355328 -> 4096 <= (V 42%nat) <= 140737488355320 -> aligned (V 42%nat) 16 -> (2147446784 + 17592186048512 <= (V 42%nat) \/ (V 42%nat) + 8 <= 2147446784) ->
  L5KA.zeros_at M (((V 42%nat) / 8) + 2147450880) 1 -> L5.writable RSEGS M (V 42%nat) 8 -> (((V 2%nat) - 128) + 128 <= (V 42%nat) \/ (V 42%nat) + 8 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 32 <= (V 42%nat) \/ (V 42%nat) + 8 <= (V 33%nat)) ->
  ((V 34%nat) + 32 <= (V 42%nat) \/ (V 42%nat) + 8 <= (V 34%nat)) -> ((V 40%nat) + 128 <= (V 42%nat) \/ (V 42%nat) + 8 <= (V 40%nat)) -> ((V 41%nat) + 1 <= (V 42%nat) \/ (V 42%nat) + 8 <= (V 41%nat)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 24) <= bv_unsigned a < ((V 33%nat) + 24) + 8) -> ~ (((V 42%nat) + 0) <= bv_unsigned a < ((V 42%nat) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 24) <= i < ((V 33%nat) + 24) + 8) -> ~ (((V 42%nat) + 0) <= i < ((V 42%nat) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x91b3c M) (st fx' R' 0x5e0d4 M')
        /\ (forall x, In x KS_acC -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 596876
        /\ getr R' (reg 11) = Z_to_bv 64 (V 39%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (8 * (V 37%nat))
        /\ getr R' (reg 19) = Z_to_bv 64 ((V 34%nat) + 24)
        /\ L5.u64_at RSEGS M' (V 42%nat) 0
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 24) (V 42%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] [HV41l HV41r] [HV42l HV42r] [HV43l HV43r] G1 G2 G8 G9 G10 G18 G19 G20 G21 G22 G23 G24 G25 G26 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 K14 K15 K16 K17 K18 [K19l K19r] K20 [K21l K21r] K22 K23 [K24l K24r] K25 [K26l K26r] K27 [K28l K28r] [K29l K29r] K30 K31 K32 K33 K34 K35 K36 K37 K38.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 42%nat => Z_to_bv 64 (V 42%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 42%nat => (V 42%nat) | 43%nat => (V 43%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 44%nat. }
  assert (HR: regs_ok E PacC.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PacC.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PacC.kn0).
  { unfold know_ok, PacC.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16 K34) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16 K34) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16 K34) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K16 K34; lia | clear - HV2l HV2r K0l K0r K11 K16 K34; lia | clear - HV2l HV2r K0l K0r K11 K16 K34; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17 K35) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17 K35) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17 K35) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17 K35) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K17 K35; lia | clear - HV33l HV33r K6l K6r K8 K11 K17 K35; lia | clear - HV33l HV33r K6l K6r K8 K11 K17 K35; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17 K35) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K17 K35; lia | clear - HV33l HV33r K6l K6r K8 K11 K17 K35; lia | clear - HV33l HV33r K6l K6r K8 K11 K17 K35; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17 K35) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17 K36) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17 K36) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17 K36) | evalEk ZA ltac:(clear) | generalize K14; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17 K36) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K12l K12r K14 K16 K17 K36; lia | clear - HV34l HV34r K12l K12r K14 K16 K17 K36; lia | clear - HV34l HV34r K12l K12r K14 K16 K17 K36; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17 K36) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17 K36) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17 K35) | evalEk ZA ltac:(clear - HV35l HV35r K19l K19r) | clear - HV33l HV33r K6l K6r K8 K11 K17 K35; lia | clear - HV33l HV33r K6l K6r K8 K11 K17 K35; lia | byte_tac ltac:(clear - HV35l HV35r K19l K19r) | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K19l K19r) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17 K36) | evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K22) | clear - HV34l HV34r K12l K12r K14 K16 K17 K36; lia | clear - HV34l HV34r K12l K12r K14 K16 K17 K36; lia | byte_tac ltac:(clear - HV36l HV36r K21l K21r K22) | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K22) | exact (conj K21l K21r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV36l HV36r K21l K21r K22) | clear; lia | rewrite (L5K.land1_bit0_true (V 36%nat) ltac:(clear - HV36l HV36r K21l K21r K22; lia) K22); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17 K36) | evalEk ZA ltac:(clear - HV37l HV37r K24l K24r) | clear - HV34l HV34r K12l K12r K14 K16 K17 K36; lia | clear - HV34l HV34r K12l K12r K14 K16 K17 K36; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17 K36) | evalEk ZA ltac:(clear - HV38l HV38r K26l K26r) | clear - HV34l HV34r K12l K12r K14 K16 K17 K36; lia | clear - HV34l HV34r K12l K12r K14 K16 K17 K36; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17 K36) | evalEk ZA ltac:(clear - HV39l HV39r K28l K28r) | clear - HV34l HV34r K12l K12r K14 K16 K17 K36; lia | clear - HV34l HV34r K12l K12r K14 K16 K17 K36; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K28l K28r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38) | clear; lia | exact K30]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38; lia | clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38; lia | clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38; lia | clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38; lia | clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K16 K34) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K12l K12r K14 K16 K17 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV41l HV41r K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (PacC.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PacC.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 33%nat) + 24) <= bv_unsigned a < ((V 33%nat) + 24) + 8) -> ~ (((V 42%nat) + 0) <= bv_unsigned a < ((V 42%nat) + 0) + 8) -> M' a = M a).
  { intros a Hn0 Hn1. apply Hfr. unfold PacC.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K17 K35 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38) | evalEk' ZA Hag ltac:(clear) | clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38 Hn1; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PacC.ps0) with 0x5e0d4 in Hms. change (SR.ps_regs PacC.ps0) with (map (fun i => (i, nth i PacC.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PacC.ps0) with PacC.cells0 in Hcells. unfold PacC.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PacC.regs0 PacC.regs_out0 56 KS_acC KS_acC_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PacC.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PacC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacC.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PacC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacC.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PacC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacC.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PacC.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11 K17 K35) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K29l K29r K31 K34 K35 K36 K37 K38) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PacD := LibSegZ_acD.
Definition KS_acD : list nat := Eval vm_compute in (BG.kept_list 56 PacD.regs0 PacD.regs_out0).
Lemma KS_acD_ok : BG.kept_ok 56 PacD.regs0 PacD.regs_out0 KS_acD = true. Proof. vm_compute. reflexivity. Qed.
Lemma acD_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 18) = Z_to_bv 64 (V 40%nat) -> getr R (reg 23) = Z_to_bv 64 (((V 40%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 40%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 52%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 53%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 54%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 55%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 128) 0 -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 40%nat) ->
  4096 <= (V 40%nat) <= 140737488355200 -> aligned (V 40%nat) 32 -> L5.defined M (V 40%nat) 128 -> L5.writable RSEGS M (V 40%nat) 128 ->
  (2147446784 + 17592186048512 <= (V 40%nat) \/ (V 40%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 40%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 40%nat) + 120) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 41%nat) 1 -> (2147446784 + 17592186048512 <= (V 41%nat) \/ (V 41%nat) + 1 <= 2147446784) -> ((V 40%nat) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 40%nat)) -> (((V 2%nat) - 128) + 128 <= (V 40%nat) \/ (V 40%nat) + 128 <= ((V 2%nat) - 128)) ->
  (((V 2%nat) - 128) + 128 <= (V 41%nat) \/ (V 41%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 33%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 128 <= (V 33%nat)) -> ((V 33%nat) + 32 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 33%nat)) -> ((((V 33%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 16 <= (((V 33%nat) / 8) + 2147450880)) ->
  ((V 34%nat) + 32 <= (V 40%nat) \/ (V 40%nat) + 128 <= (V 34%nat)) -> ((V 34%nat) + 32 <= (V 41%nat) \/ (V 41%nat) + 1 <= (V 34%nat)) -> ((((V 34%nat) / 8) + 2147450880) + 4 <= (((V 40%nat) / 8) + 2147450880) \/ (((V 40%nat) / 8) + 2147450880) + 16 <= (((V 34%nat) / 8) + 2147450880)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 8) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 40%nat) + 0) <= i < ((V 40%nat) + 0) + 8) -> ~ ((((V 40%nat) / 8) + 2147450880) <= i < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= i < ((V 41%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x91b8c M) (st fx' R' 0x91c54 M')
        /\ (forall x, In x KS_acD -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 52%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 53%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 54%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 55%nat)
        /\ L5.u8_at RSEGS M' (V 41%nat) 0
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450891) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450890) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450889) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450895) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450894) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450893) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450892) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 40%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 40%nat) 1172321806
        /\ L5.defined M' ((V 40%nat) + 8) 120).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV40l HV40r] [HV41l HV41r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] [HV52l HV52r] [HV53l HV53r] [HV54l HV54r] [HV55l HV55r] G1 G2 G8 G9 G18 G23 G24 G25 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 [K20l K20r] K21 K22 K23 K24 K25 K26 [K27l K27r] K28 K29 K30 K31 K32 K33 K34 K35 K36 K37 K38.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | 55%nat => Z_to_bv 64 (V 55%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | 54%nat => (V 54%nat) | 55%nat => (V 55%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 56%nat. }
  assert (HR: regs_ok E PacD.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PacD.regs0 nth]. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PacD.kn0).
  { unfold know_ok, PacD.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV52l HV52r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV53l HV53r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV54l HV54r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV55l HV55r) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | clear - HV2l HV2r K0l K0r K31 K32; lia | clear - HV2l HV2r K0l K0r K31 K32; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | exact (conj K20l K20r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | clear; lia | exact K21]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38; lia | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38; lia | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38; lia | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38; lia | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38; lia | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38; lia | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38; lia | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk ZA ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34 K37) | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38; lia | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34 K37) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34 K37) | evalEk ZA ltac:(clear) | clear - HV41l HV41r K27l K27r K29 K30 K32 K34 K37; lia | clear - HV41l HV41r K27l K27r K29 K30 K32 K34 K37; lia | clear - HV41l HV41r K27l K27r K29 K30 K32 K34 K37; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34 K37) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34 K37) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K31 K32) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34 K37) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K33 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K33 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34 K37) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K33 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34 K37) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV34l HV34r K36 K37 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_nil. }
  destruct (PacD.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PacD.NX0 with 56%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 40%nat) + 0) <= bv_unsigned a < ((V 40%nat) + 0) + 8) -> ~ ((((V 40%nat) / 8) + 2147450880) <= bv_unsigned a < (((V 40%nat) / 8) + 2147450880) + 16) -> ~ (((V 41%nat) + 0) <= bv_unsigned a < ((V 41%nat) + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PacD.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34 K37) | evalEk' ZA Hag ltac:(clear) | clear - HV41l HV41r K27l K27r K29 K30 K32 K34 K37 Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PacD.ps0) with 0x91c54 in Hms. change (SR.ps_regs PacD.ps0) with (map (fun i => (i, nth i PacD.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PacD.ps0) with PacD.cells0 in Hcells. unfold PacD.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PacD.regs0 PacD.regs_out0 56 KS_acD KS_acD_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PacD.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PacD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacD.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PacD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacD.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PacD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacD.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PacD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacD.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PacD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacD.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PacD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacD.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PacD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacD.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PacD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacD.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PacD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacD.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PacD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacD.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PacD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacD.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PacD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacD.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PacD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PacD.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PacD.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV41l HV41r K27l K27r K29 K30 K32 K34 K37) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV40l HV40r K20l K20r K24 K30 K31 K33 K35 K36 K38) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

End L5ACPYP.
