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
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegZ_vshA LibSegZ_vshA0 LibSegZ_vshBi LibSegZ_vshBd LibSegZ_vshI LibSegZ_vshL LibSegZ_vshE.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).   (* [comment removed for export] *)

Module L5ASHLP.
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
Module PvshA := LibSegZ_vshA.
Definition KS_vshA : list nat := Eval vm_compute in (BG.kept_list 64 PvshA.regs0 PvshA.regs_out0).
Lemma KS_vshA_ok : BG.kept_ok 64 PvshA.regs0 PvshA.regs_out0 KS_vshA = true. Proof. vm_compute. reflexivity. Qed.
Lemma vshA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 (V 41%nat) ->
  140735332487232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 64) + 64 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 64)) ->
  1 <= (V 41%nat) <= 63 -> L5.u64_at RSEGS M ((V 33%nat) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93a50 M) (st fx' R' 0x8f810 M')
        /\ (forall x, In x KS_vshA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 605076
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 34%nat) + 1)
        /\ getr R' (reg 12) = Z_to_bv 64 908088
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 33%nat) / 8)
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV41l HV41r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 41%nat => (V 41%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 42%nat. }
  assert (HR: regs_ok E PvshA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvshA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvshA.kn0).
  { unfold know_ok, PvshA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV34l HV34r K14l K14r) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_nil. }
  destruct (PvshA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvshA.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvshA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvshA.ps0) with 0x8f810 in Hms. change (SR.ps_regs PvshA.ps0) with (map (fun i => (i, nth i PvshA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvshA.ps0) with PvshA.cells0 in Hcells. unfold PvshA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvshA.regs0 PvshA.regs_out0 64 KS_vshA KS_vshA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvshA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvshA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvshA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvshA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvshA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvshA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvshA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvshA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PvshA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PvshA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PvshA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PvshA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvshA0 := LibSegZ_vshA0.
Definition KS_vshA0 : list nat := Eval vm_compute in (BG.kept_list 64 PvshA0.regs0 PvshA0.regs_out0).
Lemma KS_vshA0_ok : BG.kept_ok 64 PvshA0.regs0 PvshA0.regs_out0 KS_vshA0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma vshA0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 33%nat) -> getr R (reg 11) = Z_to_bv 64 0 ->
  140735332487232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 64) + 64 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 64)) ->
  L5.u64_at RSEGS M ((V 33%nat) + 8) (V 34%nat) -> 0 <= (V 34%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 64) <= i < ((V 2%nat) - 64) + 64) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93a50 M) (st fx' R' 0x90780 M')
        /\ (forall x, In x KS_vshA0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 605328
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 64)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 908088
        /\ getr R' (reg 18) = Z_to_bv 64 ((V 33%nat) + 8)
        /\ getr R' (reg 19) = Z_to_bv 64 2147450880
        /\ getr R' (reg 20) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880)
        /\ getr R' (reg 21) = Z_to_bv 64 ((V 33%nat) / 8)
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 8) (bv_unsigned (getr R (reg 1)))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] G2 G10 G11 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 K12 [K13l K13r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 35%nat. }
  assert (HR: regs_ok E PvshA0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvshA0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvshA0.kn0).
  { unfold know_ok, PvshA0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV34l HV34r K13l K13r) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_nil. }
  destruct (PvshA0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvshA0.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 2%nat) - 64) <= bv_unsigned a < ((V 2%nat) - 64) + 64) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvshA0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvshA0.ps0) with 0x90780 in Hms. change (SR.ps_regs PvshA0.ps0) with (map (fun i => (i, nth i PvshA0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvshA0.ps0) with PvshA0.cells0 in Hcells. unfold PvshA0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvshA0.regs0 PvshA0.regs_out0 64 KS_vshA0 KS_vshA0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvshA0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvshA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvshA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvshA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvshA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvshA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvshA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvshA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PvshA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PvshA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PvshA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshA0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PvshA0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvshBi := LibSegZ_vshBi.
Definition KS_vshBi : list nat := Eval vm_compute in (BG.kept_list 64 PvshBi.regs0 PvshBi.regs_out0).
Lemma KS_vshBi_ok : BG.kept_ok 64 PvshBi.regs0 PvshBi.regs_out0 KS_vshBi = true. Proof. vm_compute. reflexivity. Qed.
Lemma vshBi_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 41%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) / 8) -> getr R (reg 22) = Z_to_bv 64 0 ->
  140735332487232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 64) + 64 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 64)) ->
  1 <= (V 41%nat) <= 63 -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) -> 0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = false ->
  L5.u64_at RSEGS M ((V 33%nat) + 8) 2 -> L5.u64_at RSEGS M ((V 33%nat) + 24) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 33%nat) + 24) <= bv_unsigned a < ((V 33%nat) + 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 33%nat) + 24) <= i < ((V 33%nat) + 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93b94 M) (st fx' R' 0x93c2c M')
        /\ (forall x, In x KS_vshBi -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 33%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 1
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (((-1) * (V 41%nat)) + 64)
        /\ bv_unsigned (getr R' (reg 14)) = ((((18446744073709551615 * ((18446744073709551615 * 2 ^ ((V 41%nat) mod 64)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)
        /\ getr R' (reg 15) = Z_to_bv 64 ((V 33%nat) + 16)
        /\ getr R' (reg 16) = Z_to_bv 64 16
        /\ getr R' (reg 21) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((V 33%nat) + 24) 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV35l HV35r] [HV41l HV41r] [HV43l HV43r] [HV54l HV54r] G1 G2 G8 G9 G10 G18 G19 G20 G21 G22 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 K16 K17.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 35%nat => (V 35%nat) | 41%nat => (V 41%nat) | 43%nat => (V 43%nat) | 54%nat => (V 54%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PvshBi.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvshBi.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvshBi.kn0).
  { unfold know_ok, PvshBi.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | clear - HV2l HV2r K0l K0r K11; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K12l K12r) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear - HV35l HV35r K14l K14r K15) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | byte_tac ltac:(clear - HV35l HV35r K14l K14r K15) | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K14l K14r K15) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K14l K14r K15) | clear; lia | rewrite (L5K.land1_bit0_false (V 35%nat) ltac:(clear - HV35l HV35r K14l K14r K15; lia) K15); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11; lia | clear - HV33l HV33r K6l K6r K8 K11; lia | exactA K17]. }
    apply Forall_nil. }
  destruct (PvshBi.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvshBi.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((V 33%nat) + 24) <= bv_unsigned a < ((V 33%nat) + 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvshBi.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvshBi.ps0) with 0x93c2c in Hms. change (SR.ps_regs PvshBi.ps0) with (map (fun i => (i, nth i PvshBi.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvshBi.ps0) with PvshBi.cells0 in Hcells. unfold PvshBi.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvshBi.regs0 PvshBi.regs_out0 64 KS_vshBi KS_vshBi_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvshBi.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvshBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshBi.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvshBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshBi.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvshBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshBi.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvshBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshBi.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvshBi.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvshBi.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvshBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshBi.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PvshBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshBi.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PvshBi.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV33l HV33r K6l K6r K8 K11) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvshBd := LibSegZ_vshBd.
Definition KS_vshBd : list nat := Eval vm_compute in (BG.kept_list 64 PvshBd.regs0 PvshBd.regs_out0).
Lemma KS_vshBd_ok : BG.kept_ok 64 PvshBd.regs0 PvshBd.regs_out0 KS_vshBd = true. Proof. vm_compute. reflexivity. Qed.
Lemma vshBd_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 54%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 41%nat) -> getr R (reg 10) = Z_to_bv 64 (V 54%nat) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 ((V 33%nat) / 8) -> getr R (reg 22) = Z_to_bv 64 0 ->
  140735332487232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 64) + 64 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 64)) ->
  4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 8 -> 4104 <= ((V 36%nat) + (8 * (V 37%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 2147446784) ->
  1 <= (V 37%nat) <= 134217728 -> L5.writable RSEGS M (V 36%nat) (8 * (V 37%nat)) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) (V 37%nat) -> ((V 36%nat) + (8 * (V 37%nat)) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + (V 37%nat) <= (V 36%nat)) ->
  (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= ((V 2%nat) - 64)) -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 33%nat)) -> 1 <= (V 41%nat) <= 63 -> L5.u8_at RSEGS M (V 33%nat) (V 35%nat) ->
  0 <= (V 35%nat) <= 255 -> Z.testbit (V 35%nat) 0 = true -> 1 <= (V 34%nat) <= 134217728 -> 1 <= (((-1) * (V 34%nat)) + (V 37%nat)) <= 134217728 ->
  L5.u64_at RSEGS M ((V 33%nat) + 8) ((V 34%nat) + 1) -> L5.u64_at RSEGS M ((V 33%nat) + 24) (V 36%nat) -> L5.u64_at RSEGS M ((8 * (V 34%nat)) + (V 36%nat)) 0 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ ((((V 36%nat) + (8 * (V 34%nat))) + 0) <= bv_unsigned a < (((V 36%nat) + (8 * (V 34%nat))) + 0) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((((V 36%nat) + (8 * (V 34%nat))) + 0) <= i < (((V 36%nat) + (8 * (V 34%nat))) + 0) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93b94 M) (st fx' R' 0x93c2c M')
        /\ (forall x, In x KS_vshBd -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((8 * (V 34%nat)) + (V 36%nat))
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 (((-1) * (V 41%nat)) + 64)
        /\ bv_unsigned (getr R' (reg 14)) = ((((18446744073709551615 * ((18446744073709551615 * 2 ^ ((V 41%nat) mod 64)) mod 2 ^ 64)) mod 2 ^ 64) + 18446744073709551615) mod 2 ^ 64)
        /\ getr R' (reg 15) = Z_to_bv 64 (((8 * (V 34%nat)) + (V 36%nat)) - 8)
        /\ getr R' (reg 16) = Z_to_bv 64 ((8 * (V 34%nat)) + 8)
        /\ getr R' (reg 21) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' ((8 * (V 34%nat)) + (V 36%nat)) 0).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV35l HV35r] [HV36l HV36r] [HV37l HV37r] [HV41l HV41r] [HV43l HV43r] [HV54l HV54r] G1 G2 G8 G9 G10 G18 G19 G20 G21 G22 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 [K16l K16r] K17 K18 K19 K20 K21 [K22l K22r] K23 [K24l K24r] K25 [K26l K26r] [K27l K27r] K28 K29 K30.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 35%nat => Z_to_bv 64 (V 35%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 54%nat => Z_to_bv 64 (V 54%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 35%nat => (V 35%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 41%nat => (V 41%nat) | 43%nat => (V 43%nat) | 54%nat => (V 54%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 55%nat. }
  assert (HR: regs_ok E PvshBd.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvshBd.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvshBd.kn0).
  { unfold know_ok, PvshBd.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K27l K27r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K27l K27r) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K27l K27r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K27l K27r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K27l K27r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K27l K27r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K27l K27r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K27l K27r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K27l K27r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K27l K27r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K27l K27r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K27l K27r) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K27l K27r) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K27l K27r) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K27l K27r) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord1; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K25) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | byte_tac ltac:(clear - HV35l HV35r K24l K24r K25) | exactA K23]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K25) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange_andlit; [evalEk ZA ltac:(clear - HV35l HV35r K24l K24r K25) | clear; lia | rewrite (L5K.land1_bit0_true (V 35%nat) ltac:(clear - HV35l HV35r K24l K24r K25; lia) K25); clear; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K27l K27r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K27l K27r HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K27l K27r) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV34l HV34r K26l K26r K27l K27r HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear) | clear - HV34l HV34r K26l K26r K27l K27r HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21; lia | clear - HV34l HV34r K26l K26r K27l K27r HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21; lia | exactA K30]. }
    apply Forall_nil. }
  destruct (PvshBd.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvshBd.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((((V 36%nat) + (8 * (V 34%nat))) + 0) <= bv_unsigned a < (((V 36%nat) + (8 * (V 34%nat))) + 0) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvshBd.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV34l HV34r K26l K26r K27l K27r HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk' ZA Hag ltac:(clear) | clear - HV34l HV34r K26l K26r K27l K27r HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvshBd.ps0) with 0x93c2c in Hms. change (SR.ps_regs PvshBd.ps0) with (map (fun i => (i, nth i PvshBd.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvshBd.ps0) with PvshBd.cells0 in Hcells. unfold PvshBd.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvshBd.regs0 PvshBd.regs_out0 64 KS_vshBd KS_vshBd_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvshBd.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvshBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshBd.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvshBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshBd.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvshBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshBd.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PvshBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshBd.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PvshBd.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvshBd.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvshBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshBd.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PvshBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshBd.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PvshBd.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV34l HV34r K26l K26r K27l K27r HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk' ZA Hag ltac:(clear) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvshI := LibSegZ_vshI.
Definition KS_vshI : list nat := Eval vm_compute in (BG.kept_list 64 PvshI.regs0 PvshI.regs_out0).
Lemma KS_vshI_ok : BG.kept_ok 64 PvshI.regs0 PvshI.regs_out0 KS_vshI = true. Proof. vm_compute. reflexivity. Qed.
Lemma vshI_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 41%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 36%nat) + (8 * (V 40%nat))) -> getr R (reg 11) = Z_to_bv 64 (V 40%nat) -> getr R (reg 12) = Z_to_bv 64 (V 39%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) -> getr R (reg 14) = Z_to_bv 64 (V 53%nat) -> getr R (reg 15) = Z_to_bv 64 (((V 36%nat) + (8 * (V 40%nat))) - 8) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 0 ->
  140735332487232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 64) + 64 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 64)) ->
  4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 8 -> 4104 <= ((V 36%nat) + (8 * (V 37%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 2147446784) ->
  1 <= (V 37%nat) <= 134217728 -> L5.writable RSEGS M (V 36%nat) (8 * (V 37%nat)) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) (V 37%nat) -> ((V 36%nat) + (8 * (V 37%nat)) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + (V 37%nat) <= (V 36%nat)) ->
  (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= ((V 2%nat) - 64)) -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 33%nat)) -> 1 <= (V 41%nat) <= 63 -> 0 <= (V 39%nat) <= 18446744073709551615 ->
  0 <= (V 38%nat) <= 18446744073709551615 -> 1 <= (V 34%nat) <= 134217728 -> 1 <= (V 52%nat) <= 63 -> 0 <= (V 53%nat) <= 18446744073709551615 ->
  1 <= ((V 37%nat) - (V 40%nat)) <= 134217728 -> L5.u64_at RSEGS M (((V 36%nat) + (8 * (V 40%nat))) - 8) (V 38%nat) -> 2 <= (V 40%nat) <= 134217728 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 36%nat) + (8 * (V 40%nat))) - 8) + 0) <= bv_unsigned a < ((((V 36%nat) + (8 * (V 40%nat))) - 8) + 0) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 36%nat) + (8 * (V 40%nat))) - 8) + 0) <= i < ((((V 36%nat) + (8 * (V 40%nat))) - 8) + 0) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93c2c M) (st fx' R' 0x93c2c M')
        /\ (forall x, In x KS_vshI -> getr R' (reg x) = getr R (reg x))
        /\ bv_unsigned (getr R' (reg 5)) = (Z.land ((V 38%nat) / 2 ^ ((V 52%nat) mod 64)) (V 53%nat))
        /\ getr R' (reg 10) = Z_to_bv 64 (((V 36%nat) + (8 * (V 40%nat))) - 8)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 40%nat) - 1)
        /\ bv_unsigned (getr R' (reg 12)) = (((V 38%nat) * 2 ^ ((V 41%nat) mod 64)) mod 2 ^ 64)
        /\ getr R' (reg 15) = Z_to_bv 64 (((V 36%nat) + (8 * (V 40%nat))) - 16)
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 36%nat) + (8 * (V 40%nat))) - 8)
        /\ getr R' (reg 17) = Z_to_bv 64 (((((V 36%nat) + (8 * (V 40%nat))) - 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' (((V 36%nat) + (8 * (V 40%nat))) - 8) (((V 38%nat) * 2 ^ ((V 41%nat) mod 64)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + (8 * (V 40%nat))) (Z.lor (Z.land ((V 38%nat) / 2 ^ ((V 52%nat) mod 64)) (V 53%nat)) (V 39%nat))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] [HV41l HV41r] [HV43l HV43r] [HV52l HV52r] [HV53l HV53r] G1 G2 G8 G9 G10 G11 G12 G13 G14 G15 G18 G19 G20 G21 G22 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 [K16l K16r] K17 K18 K19 K20 K21 [K22l K22r] [K23l K23r] [K24l K24r] [K25l K25r] [K26l K26r] [K27l K27r] [K28l K28r] K29 [K30l K30r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 43%nat => (V 43%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PvshI.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvshI.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvshI.kn0).
  { unfold know_ok, PvshI.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K28l K28r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K28l K28r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K28l K28r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K28l K28r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K28l K28r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K28l K28r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K28l K28r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K27l K27r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r HV40l HV40r K30l K30r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV40l HV40r K28l K28r K30l K30r) | evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV40l HV40r K28l K28r K30l K30r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV40l HV40r K28l K28r K30l K30r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K28l K28r K30l K30r) | exact (conj K30l K30r)]. }
    apply Forall_nil. }
  destruct (PvshI.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvshI.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((((V 36%nat) + (8 * (V 40%nat))) - 8) + 0) <= bv_unsigned a < ((((V 36%nat) + (8 * (V 40%nat))) - 8) + 0) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvshI.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV40l HV40r K28l K28r K30l K30r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV40l HV40r K28l K28r K30l K30r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvshI.ps0) with 0x93c2c in Hms. change (SR.ps_regs PvshI.ps0) with (map (fun i => (i, nth i PvshI.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvshI.ps0) with PvshI.cells0 in Hcells. unfold PvshI.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvshI.regs0 PvshI.regs_out0 64 KS_vshI KS_vshI_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvshI.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PvshI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvshI.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvshI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshI.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvshI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshI.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvshI.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvshI.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvshI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshI.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PvshI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshI.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PvshI.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV40l HV40r K28l K28r K30l K30r) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV40l HV40r K28l K28r K30l K30r) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvshL := LibSegZ_vshL.
Definition KS_vshL : list nat := Eval vm_compute in (BG.kept_list 64 PvshL.regs0 PvshL.regs_out0).
Lemma KS_vshL_ok : BG.kept_ok 64 PvshL.regs0 PvshL.regs_out0 KS_vshL = true. Proof. vm_compute. reflexivity. Qed.
Lemma vshL_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 40%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 53%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) -> getr R (reg 9) = Z_to_bv 64 (V 41%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 36%nat) + (8 * (V 40%nat))) -> getr R (reg 11) = Z_to_bv 64 (V 40%nat) -> getr R (reg 12) = Z_to_bv 64 (V 39%nat) -> getr R (reg 13) = Z_to_bv 64 (V 52%nat) -> getr R (reg 14) = Z_to_bv 64 (V 53%nat) -> getr R (reg 15) = Z_to_bv 64 (((V 36%nat) + (8 * (V 40%nat))) - 8) -> getr R (reg 18) = Z_to_bv 64 ((V 33%nat) + 8) -> getr R (reg 19) = Z_to_bv 64 2147450880 -> getr R (reg 20) = Z_to_bv 64 ((((V 33%nat) + 8) / 8) + 2147450880) -> getr R (reg 21) = Z_to_bv 64 (((V 33%nat) / 8) + 2147450880) -> getr R (reg 22) = Z_to_bv 64 0 ->
  140735332487232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> 4096 <= (V 33%nat) <= 140737488355296 -> aligned (V 33%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 33%nat) \/ (V 33%nat) + 32 <= 2147446784) -> L5KA.zeros_at M (((V 33%nat) / 8) + 2147450880) 4 -> L5.writable RSEGS M (V 33%nat) 32 -> (((V 2%nat) - 64) + 64 <= (V 33%nat) \/ (V 33%nat) + 32 <= ((V 2%nat) - 64)) ->
  4096 <= (V 36%nat) <= 140737488355328 -> aligned (V 36%nat) 8 -> 4104 <= ((V 36%nat) + (8 * (V 37%nat))) <= 140737479966720 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= 2147446784) ->
  1 <= (V 37%nat) <= 134217728 -> L5.writable RSEGS M (V 36%nat) (8 * (V 37%nat)) -> L5KA.zeros_at M (((V 36%nat) / 8) + 2147450880) (V 37%nat) -> ((V 36%nat) + (8 * (V 37%nat)) <= (((V 36%nat) / 8) + 2147450880) \/ (((V 36%nat) / 8) + 2147450880) + (V 37%nat) <= (V 36%nat)) ->
  (((V 2%nat) - 64) + 64 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= ((V 2%nat) - 64)) -> ((V 33%nat) + 16 <= (V 36%nat) \/ (V 36%nat) + (8 * (V 37%nat)) <= (V 33%nat)) -> 1 <= (V 41%nat) <= 63 -> 0 <= (V 39%nat) <= 18446744073709551615 ->
  0 <= (V 38%nat) <= 18446744073709551615 -> 1 <= (V 34%nat) <= 134217728 -> 1 <= (V 52%nat) <= 63 -> 0 <= (V 53%nat) <= 18446744073709551615 ->
  1 <= ((V 37%nat) - (V 40%nat)) <= 134217728 -> L5.u64_at RSEGS M (((V 36%nat) + (8 * (V 40%nat))) - 8) (V 38%nat) -> 1 <= (V 40%nat) <= 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((((V 36%nat) + (8 * (V 40%nat))) - 8) + 0) <= bv_unsigned a < ((((V 36%nat) + (8 * (V 40%nat))) - 8) + 0) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((((V 36%nat) + (8 * (V 40%nat))) - 8) + 0) <= i < ((((V 36%nat) + (8 * (V 40%nat))) - 8) + 0) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93c2c M) (st fx' R' 0x90780 M')
        /\ (forall x, In x KS_vshL -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 605328
        /\ bv_unsigned (getr R' (reg 5)) = (Z.land ((V 38%nat) / 2 ^ ((V 52%nat) mod 64)) (V 53%nat))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ bv_unsigned (getr R' (reg 12)) = (((V 38%nat) * 2 ^ ((V 41%nat) mod 64)) mod 2 ^ 64)
        /\ getr R' (reg 15) = Z_to_bv 64 (((V 36%nat) + (8 * (V 40%nat))) - 16)
        /\ getr R' (reg 16) = Z_to_bv 64 (((V 36%nat) + (8 * (V 40%nat))) - 8)
        /\ getr R' (reg 17) = Z_to_bv 64 (((((V 36%nat) + (8 * (V 40%nat))) - 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M' (((V 36%nat) + (8 * (V 40%nat))) - 8) (((V 38%nat) * 2 ^ ((V 41%nat) mod 64)) mod 2 ^ 64)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + (8 * (V 40%nat))) (Z.lor (Z.land ((V 38%nat) / 2 ^ ((V 52%nat) mod 64)) (V 53%nat)) (V 39%nat))).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV34l HV34r] [HV36l HV36r] [HV37l HV37r] [HV38l HV38r] [HV39l HV39r] [HV40l HV40r] [HV41l HV41r] [HV43l HV43r] [HV52l HV52r] [HV53l HV53r] G1 G2 G8 G9 G10 G11 G12 G13 G14 G15 G18 G19 G20 G21 G22 [K0l K0r] K1 K2 K3 K4 K5 [K6l K6r] K7 K8 K9 K10 K11 [K12l K12r] K13 [K14l K14r] K15 [K16l K16r] K17 K18 K19 K20 K21 [K22l K22r] [K23l K23r] [K24l K24r] [K25l K25r] [K26l K26r] [K27l K27r] [K28l K28r] K29 [K30l K30r].
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 34%nat => Z_to_bv 64 (V 34%nat) | 36%nat => Z_to_bv 64 (V 36%nat) | 37%nat => Z_to_bv 64 (V 37%nat) | 38%nat => Z_to_bv 64 (V 38%nat) | 39%nat => Z_to_bv 64 (V 39%nat) | 40%nat => Z_to_bv 64 (V 40%nat) | 41%nat => Z_to_bv 64 (V 41%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 52%nat => Z_to_bv 64 (V 52%nat) | 53%nat => Z_to_bv 64 (V 53%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 34%nat => (V 34%nat) | 36%nat => (V 36%nat) | 37%nat => (V 37%nat) | 38%nat => (V 38%nat) | 39%nat => (V 39%nat) | 40%nat => (V 40%nat) | 41%nat => (V 41%nat) | 43%nat => (V 43%nat) | 52%nat => (V 52%nat) | 53%nat => (V 53%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 54%nat. }
  assert (HR: regs_ok E PvshL.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvshL.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvshL.kn0).
  { unfold know_ok, PvshL.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | clear - HV2l HV2r K0l K0r K11 K20; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K8; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | clear - HV33l HV33r K6l K6r K8 K11 K21; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | generalize K11; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | exact (conj K12l K12r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | clear; lia | exact K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K28l K28r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | exact (conj K16l K16r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K28l K28r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K28l K28r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K28l K28r; lia | exactA K17]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K28l K28r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K28l K28r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV37l HV37r K16l K16r K28l K28r; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r K11 K20) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV33l HV33r K6l K6r K8 K11 K21) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21) | evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV34l HV34r K25l K25r) | exact (conj K25l K25r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K26l K26r) | exact (conj K26l K26r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV53l HV53r K27l K27r) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K14l K14r K15 K16l K16r K19 K20 K21 K28l K28r HV40l HV40r K30l K30r) | exact (conj K28l K28r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV40l HV40r K28l K28r K30l K30r) | evalEk ZA ltac:(clear - HV38l HV38r K24l K24r) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV40l HV40r K28l K28r K30l K30r; lia | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV40l HV40r K28l K28r K30l K30r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV40l HV40r K28l K28r K30l K30r) | exact (conj K30l K30r)]. }
    apply Forall_nil. }
  destruct (PvshL.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvshL.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, ~ (((((V 36%nat) + (8 * (V 40%nat))) - 8) + 0) <= bv_unsigned a < ((((V 36%nat) + (8 * (V 40%nat))) - 8) + 0) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PvshL.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV40l HV40r K28l K28r K30l K30r) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV40l HV40r K28l K28r K30l K30r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvshL.ps0) with 0x90780 in Hms. change (SR.ps_regs PvshL.ps0) with (map (fun i => (i, nth i PvshL.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvshL.ps0) with PvshL.cells0 in Hcells. unfold PvshL.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvshL.regs0 PvshL.regs_out0 64 KS_vshL KS_vshL_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvshL.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvshL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshL.regs_out0 E' R' 5 Hregs) by (clear; lia). cbn [nth PvshL.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvshL.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvshL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshL.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PvshL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshL.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PvshL.regs_out0]. L5K.evalB' ZA Hag. den_tac. }
  split. { rewrite (BG.out_reg PvshL.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PvshL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshL.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PvshL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshL.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PvshL.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV40l HV40r K28l K28r K30l K30r) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K12l K12r K14l K14r K15 K19 K20 K21 HV40l HV40r K28l K28r K30l K30r) | (L5K.evalB' ZA Hag; den_tac) | clear; lia]. 
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Module PvshE := LibSegZ_vshE.
Definition KS_vshE : list nat := Eval vm_compute in (BG.kept_list 64 PvshE.regs0 PvshE.regs_out0).
Lemma KS_vshE_ok : BG.kept_ok 64 PvshE.regs0 PvshE.regs_out0 KS_vshE = true. Proof. vm_compute. reflexivity. Qed.
Lemma vshE_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 44%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 49%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 ->
  getr R (reg 1) = Z_to_bv 64 (V 43%nat) -> getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 64) -> getr R (reg 8) = Z_to_bv 64 (V 33%nat) ->
  140735332487232 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 64) 64 -> L5.img_clear M 860160 880640 ->
  L5.u64_at RSEGS M 908088 2147450880 -> L5.u32_at RSEGS M 908096 1 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 44%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 45%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 46%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 47%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 48%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 49%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 50%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 51%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0x93c90 M) (st fx' R' 0x93cb8 M')
        /\ (forall x, In x KS_vshE -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 44%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 45%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 48%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 49%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 51%nat)).
Proof.
  intros [HV2l HV2r] [HV33l HV33r] [HV43l HV43r] [HV44l HV44r] [HV45l HV45r] [HV46l HV46r] [HV47l HV47r] [HV48l HV48r] [HV49l HV49r] [HV50l HV50r] [HV51l HV51r] G1 G2 G8 [K0l K0r] K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 (V 2%nat) | 33%nat => Z_to_bv 64 (V 33%nat) | 43%nat => Z_to_bv 64 (V 43%nat) | 44%nat => Z_to_bv 64 (V 44%nat) | 45%nat => Z_to_bv 64 (V 45%nat) | 46%nat => Z_to_bv 64 (V 46%nat) | 47%nat => Z_to_bv 64 (V 47%nat) | 48%nat => Z_to_bv 64 (V 48%nat) | 49%nat => Z_to_bv 64 (V 49%nat) | 50%nat => Z_to_bv 64 (V 50%nat) | 51%nat => Z_to_bv 64 (V 51%nat) | _ => getr R (reg j) end) (fun _ => [])).
  assert (ZA : forall j, bv_unsigned (ev E j) = (fun j : nat => match j with 2%nat => (V 2%nat) | 33%nat => (V 33%nat) | 43%nat => (V 43%nat) | 44%nat => (V 44%nat) | 45%nat => (V 45%nat) | 46%nat => (V 46%nat) | 47%nat => (V 47%nat) | 48%nat => (V 48%nat) | 49%nat => (V 49%nat) | 50%nat => (V 50%nat) | 51%nat => (V 51%nat) | _ => bv_unsigned (getr R (reg j)) end) j).
  { BigLinkZA.za_tac0 52%nat. }
  assert (HR: regs_ok E PvshE.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PvshE.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PvshE.kn0).
  { unfold know_ok, PvshE.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV44l HV44r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV45l HV45r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV46l HV46r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV47l HV47r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV48l HV48r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV49l HV49r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV50l HV50r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear - HV51l HV51r) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K13]. }
    apply Forall_nil. }
  destruct (PvshE.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr).
  change PvshE.NX0 with 64%nat in Hag.
  exists fx', R', M'. split. exact Hgr.
  assert (FRW: forall a : word, M' a = M a).
  { intros a. apply Hfr. unfold PvshE.F0.
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PvshE.ps0) with 0x93cb8 in Hms. change (SR.ps_regs PvshE.ps0) with (map (fun i => (i, nth i PvshE.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PvshE.ps0) with PvshE.cells0 in Hcells. unfold PvshE.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PvshE.regs0 PvshE.regs_out0 64 KS_vshE KS_vshE_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PvshE.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PvshE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshE.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PvshE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshE.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PvshE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshE.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PvshE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshE.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PvshE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshE.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PvshE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshE.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PvshE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshE.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PvshE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PvshE.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PvshE.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  rewrite (BG.out_reg PvshE.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PvshE.regs_out0]. first [reflexivity | wordP' ZA Hag]. 
Qed.
(* [comment removed for export] *)

End L5ASHLP.
