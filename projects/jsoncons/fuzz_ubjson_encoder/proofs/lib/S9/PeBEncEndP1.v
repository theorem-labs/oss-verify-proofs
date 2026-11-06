(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BigLinkZA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Eb0PlanKit AsanPlanCore
     BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_038S9 BndP_Eb_039S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBENDP1.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).

Lemma word_of_zpoly E Vz e z : L5K.zagree E Vz e -> L5KA.zpolyA Vz e = Some z -> edenot E e = Z_to_bv 64 z.
Proof.
  intros A Pz. rewrite (BG.word_of_unsigned (edenot E e) (z mod BL.MM) (L5KA.zpolyA_sound E Vz e z A Pz)).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, BL.MM. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.

Lemma u64_of_KWord8a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 8 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u64_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u64_of_KWord8; eauto. Qed.
Lemma u32_of_KWord4a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 4 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> a' = a + off -> L5.u32_at RSEGS M a' v.
Proof. intros K Ha Hv ->. eapply L5K.u32_of_KWord4; eauto. Qed.
Lemma u8_of_KWord1a E M b off e a v a' : kentry_ok RSEGS E M (KWord (SA b off) 1 e) -> bv_unsigned (edenot E b) = a ->
  bv_unsigned (edenot E e) = v -> 0 <= v < 256 -> a' = a + off -> L5.u8_at RSEGS M a' v.
Proof. intros K Ha Hv Hr ->. eapply L5K.u8_of_KWord1; eauto. Qed.

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

Local Ltac solve_modk k :=
  repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (k; zfacts; lia) end;
  first [ rewrite Z.mod_small; [ first [reflexivity | k; lia] | k; L5K.zrange_tac ]
        | symmetry; eapply (Z.mod_unique_pos _ _ (-1)); k; unfold BL.MM; lia
        | symmetry; eapply (Z.mod_unique_pos _ _ 1); k; unfold BL.MM; lia ].

Local Ltac pvz_hg tac := lazymatch goal with |- ?G0 => let PG := fresh "PGoal" in set (PG := G0); tac; subst PG end.
Local Ltac pvz_fold B k := lazymatch B with | ?A2 /\ ?B2 => pvz_fold B2 ltac:(fun T2 => let T := fresh "pvzT" in pose (T := A2 /\ T2); k T) | _ => k B end.
Local Ltac pvz_linconj := lazymatch goal with |- ?A /\ ?B => pvz_fold B ltac:(fun T => change_no_check (A /\ T)) | _ => idtac end.
Local Ltac pvz_unfold ZA := lazymatch type of ZA with forall j, _ = ?f j => tryif is_var f then unfold f else idtac | _ => idtac end.
Tactic Notation "evalEk" constr(ZA) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val; [ apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].
Tactic Notation "evalEk'" constr(ZA) constr(AG) tactic(k) :=
  L5K.norm_expr; eapply L5KA.zpolyA_val;
  [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity] | cbn [L5KA.zpolyA]; pvz_unfold ZA; reflexivity | solve_modk k ].

Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.

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

Local Ltac den_tac := first [reflexivity | lia | idtac].

Local Ltac apc_norm :=
  repeat match goal with
  | |- context [APC.eadd ?a ?b] => let t := eval vm_compute in (APC.eadd a b) in change (APC.eadd a b) with t
  | |- context [APC.esub ?a ?b] => let t := eval vm_compute in (APC.esub a b) in change (APC.esub a b) with t
  | |- context [APC.escale ?c ?e] => let t := eval vm_compute in (APC.escale c e) in change (APC.escale c e) with t
  | |- context [APC.eaddz ?a ?z] => let t := eval vm_compute in (APC.eaddz a z) in change (APC.eaddz a z) with t
  end.

Local Ltac zp_norm := repeat (match goal with |- context [(?a <=? ?b) && (?c <? ?d)] => let r := eval vm_compute in ((a <=? b) && (c <? d)) in change ((a <=? b) && (c <? d)) with r end);
  repeat (match goal with |- context [2 ^ ?s] => let r := eval vm_compute in (2 ^ s) in change (2 ^ s) with r end); lazy beta iota zeta.
Local Ltac zp_mods := repeat match goal with |- context [(?x mod 18446744073709551616) / _] => rewrite (Z.mod_small x 18446744073709551616) by (zfacts; lia) end.
Local Ltac slotP ZA :=
  first [ assumption | reflexivity
        | (etransitivity; [eassumption|]; symmetry; eapply word_of_zpoly; [apply (L5K.zagree_all _ _ _ ZA) | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia]]) ].

Local Ltac wordP' ZA AG :=
  eapply word_of_zpoly; [ eapply (L5K.zagree_lt _ _ _ _ _ AG); [apply (L5K.zagree_all _ _ _ ZA) | vm_compute; reflexivity]
                        | cbn [L5KA.zpolyA]; pvz_unfold ZA; zp_norm; f_equal; zp_mods; first [reflexivity | clear; zfacts; lia | zfacts; lia] ].

Module PbqNaA := BndP_Eb_038S9.LibSegEb_bqNaA.
Definition KS_bqNaA : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaA.regs0 PbqNaA.regs_out0).
Lemma KS_bqNaA_ok : BG.kept_ok 80 PbqNaA.regs0 PbqNaA.regs_out0 KS_bqNaA = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 128) <= bv_unsigned a < ((V 2%nat) - 128) + 128) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 128) <= i < ((V 2%nat) - 128) + 128) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabafc M) (st fx' R' 0x5edb0 M')
        /\ (forall x, In x KS_bqNaA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 703344
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 10) = Z_to_bv 64 96
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = getr R (reg 12)
        /\ getr R' (reg 21) = getr R (reg 10)
        /\ getr R' (reg 25) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 104) (bv_unsigned (getr R (reg 27)))
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
  intros pvzI1 G2 K0 K1 K2 pvzI2 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as K3l; move K3l before pvzI2; pose proof (proj2 pvzI2) as K3r; move K3r before pvzI2; clear pvzI2.
  set (vz_2 := V 2%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 3%nat. }
  assert (HR: regs_ok E PbqNaA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaA.kn0).
  { unfold know_ok, PbqNaA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 128) <= bv_unsigned a < (vz_2 - 128) + 128) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbqNaA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaA.ps0) with 0x5edb0 in Hms. change (SR.ps_regs PbqNaA.ps0) with (map (fun i => (i, nth i PbqNaA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaA.ps0) with PbqNaA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaA.regs0 PbqNaA.regs_out0 80 KS_bqNaA KS_bqNaA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaA.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbqNaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbqNaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaA.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbqNaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaA.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaA.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaA.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbqNaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaA.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbqNaA.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PbqNaA.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbqNaA.regs_out0]. rewrite (BG.edenot_kept 80 E E' _ Hag) by (vm_compute; reflexivity). reflexivity. }
  split. { rewrite (BG.out_reg PbqNaA.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbqNaA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaDeq0 := BndP_Eb_038S9.LibSegEb_bqNaDeq0.
Definition KS_bqNaDeq0 : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaDeq0.regs0 PbqNaDeq0.regs_out0).
Lemma KS_bqNaDeq0_ok : BG.kept_ok 80 PbqNaDeq0.regs0 PbqNaDeq0.regs_out0 KS_bqNaDeq0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaDeq0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 10%nat) + 48) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  L5.u32_at RSEGS M ((V 10%nat) + 48) (V 43%nat) -> 1 <= (V 43%nat) <= 1024 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> aligned (V 38%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 24) / 8) + 2147450880) 3 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u32_at RSEGS M ((V 39%nat) - 24) 0 -> L5.u64_at RSEGS M ((V 39%nat) - 16) (V 46%nat) -> 0 <= (V 46%nat) <= 16777216 ->
  L5.u64_at RSEGS M ((V 39%nat) - 8) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= bv_unsigned a < ((V 10%nat) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= i < ((V 10%nat) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabb70 M) (st fx' R' 0xabd2c M')
        /\ (forall x, In x KS_bqNaDeq0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 10%nat) + 24)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 10%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880)
        /\ L5.u32_at RSEGS M' ((V 10%nat) + 48) ((V 43%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 703228
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 82866
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.defined M' ((V 47%nat) + 24) 104
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G10 G11 G12 G19 G21 G25 K0 K1 K2 pvzI13 K4 K5 pvzI14 K7 K8 K9 K10 K11 K12 K13 pvzI15 K15 K16 K17 K18 K19 K20 K21 K22 pvzI16 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 pvzI17 K35 K36 pvzI18 K38 K39 pvzI19 pvzI20 K42 K43 pvzI21 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 pvzI22 K56.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV47l; move HV47l before pvzI9; pose proof (proj2 pvzI9) as HV47r; move HV47r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV48l; move HV48l before pvzI10; pose proof (proj2 pvzI10) as HV48r; move HV48r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV56l; move HV56l before pvzI11; pose proof (proj2 pvzI11) as HV56r; move HV56r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV57l; move HV57l before pvzI12; pose proof (proj2 pvzI12) as HV57r; move HV57r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K3l; move K3l before pvzI13; pose proof (proj2 pvzI13) as K3r; move K3r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K6l; move K6l before pvzI14; pose proof (proj2 pvzI14) as K6r; move K6r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K14l; move K14l before pvzI15; pose proof (proj2 pvzI15) as K14r; move K14r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K23l; move K23l before pvzI16; pose proof (proj2 pvzI16) as K23r; move K23r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K34l; move K34l before pvzI17; pose proof (proj2 pvzI17) as K34r; move K34r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K37l; move K37l before pvzI18; pose proof (proj2 pvzI18) as K37r; move K37r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K40l; move K40l before pvzI19; pose proof (proj2 pvzI19) as K40r; move K40r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K41l; move K41l before pvzI20; pose proof (proj2 pvzI20) as K41r; move K41r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K44l; move K44l before pvzI21; pose proof (proj2 pvzI21) as K44r; move K44r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K55l; move K55l before pvzI22; pose proof (proj2 pvzI22) as K55r; move K55r before pvzI22; clear pvzI22.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | 43%nat => vz_43 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbqNaDeq0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaDeq0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaDeq0.kn0).
  { unfold know_ok, PbqNaDeq0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear; lia | exact K42]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r HV39l HV39r K41l K41r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV46l HV46r K55l K55r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K55l K55r) | exact (conj K55l K55r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV46l HV46r K55l K55r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K56]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaDeq0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaDeq0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> ~ ((vz_10 + 48) <= bv_unsigned a < (vz_10 + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbqNaDeq0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K23l K23r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaDeq0.ps0) with 0xabd2c in Hms. change (SR.ps_regs PbqNaDeq0.ps0) with (map (fun i => (i, nth i PbqNaDeq0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaDeq0.ps0) with PbqNaDeq0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaDeq0.regs0 PbqNaDeq0.regs_out0 80 KS_bqNaDeq0 KS_bqNaDeq0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaDeq0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaDeq0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaDeq0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbqNaDeq0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbqNaDeq0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbqNaDeq0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbqNaDeq0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbqNaDeq0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbqNaDeq0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbqNaDeq0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbqNaDeq0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbqNaDeq0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbqNaDeq0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq0.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbqNaDeq0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K37l K37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaDeq2 := BndP_Eb_038S9.LibSegEb_bqNaDeq2.
Definition KS_bqNaDeq2 : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaDeq2.regs0 PbqNaDeq2.regs_out0).
Lemma KS_bqNaDeq2_ok : BG.kept_ok 80 PbqNaDeq2.regs0 PbqNaDeq2.regs_out0 KS_bqNaDeq2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaDeq2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 10%nat) + 48) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  L5.u32_at RSEGS M ((V 10%nat) + 48) (V 43%nat) -> 1 <= (V 43%nat) <= 1024 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> aligned (V 38%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 24) / 8) + 2147450880) 3 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u32_at RSEGS M ((V 39%nat) - 24) 2 -> L5.u64_at RSEGS M ((V 39%nat) - 16) (V 46%nat) -> 0 <= (V 46%nat) <= 16777216 ->
  L5.u64_at RSEGS M ((V 39%nat) - 8) (V 46%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= bv_unsigned a < ((V 10%nat) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= i < ((V 10%nat) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabb70 M) (st fx' R' 0xabd2c M')
        /\ (forall x, In x KS_bqNaDeq2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 46%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 10%nat) + 24)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 10%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880)
        /\ L5.u32_at RSEGS M' ((V 10%nat) + 48) ((V 43%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 703228
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 82866
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.defined M' ((V 47%nat) + 24) 104
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 G2 G8 G9 G10 G11 G12 G19 G21 G25 K0 K1 K2 pvzI13 K4 K5 pvzI14 K7 K8 K9 K10 K11 K12 K13 pvzI15 K15 K16 K17 K18 K19 K20 K21 K22 pvzI16 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 pvzI17 K35 K36 pvzI18 K38 K39 pvzI19 pvzI20 K42 K43 pvzI21 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 pvzI22 K56.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV47l; move HV47l before pvzI9; pose proof (proj2 pvzI9) as HV47r; move HV47r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV48l; move HV48l before pvzI10; pose proof (proj2 pvzI10) as HV48r; move HV48r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV56l; move HV56l before pvzI11; pose proof (proj2 pvzI11) as HV56r; move HV56r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV57l; move HV57l before pvzI12; pose proof (proj2 pvzI12) as HV57r; move HV57r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K3l; move K3l before pvzI13; pose proof (proj2 pvzI13) as K3r; move K3r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K6l; move K6l before pvzI14; pose proof (proj2 pvzI14) as K6r; move K6r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K14l; move K14l before pvzI15; pose proof (proj2 pvzI15) as K14r; move K14r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K23l; move K23l before pvzI16; pose proof (proj2 pvzI16) as K23r; move K23r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K34l; move K34l before pvzI17; pose proof (proj2 pvzI17) as K34r; move K34r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K37l; move K37l before pvzI18; pose proof (proj2 pvzI18) as K37r; move K37r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K40l; move K40l before pvzI19; pose proof (proj2 pvzI19) as K40r; move K40r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K41l; move K41l before pvzI20; pose proof (proj2 pvzI20) as K41r; move K41r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K44l; move K44l before pvzI21; pose proof (proj2 pvzI21) as K44r; move K44r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K55l; move K55l before pvzI22; pose proof (proj2 pvzI22) as K55r; move K55r before pvzI22; clear pvzI22.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | 43%nat => vz_43 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbqNaDeq2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaDeq2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaDeq2.kn0).
  { unfold know_ok, PbqNaDeq2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear; lia | exact K42]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r HV39l HV39r K41l K41r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV46l HV46r K55l K55r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K55l K55r) | exact (conj K55l K55r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV46l HV46r K55l K55r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K56]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaDeq2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaDeq2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> ~ ((vz_10 + 48) <= bv_unsigned a < (vz_10 + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbqNaDeq2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K23l K23r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaDeq2.ps0) with 0xabd2c in Hms. change (SR.ps_regs PbqNaDeq2.ps0) with (map (fun i => (i, nth i PbqNaDeq2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaDeq2.ps0) with PbqNaDeq2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaDeq2.regs0 PbqNaDeq2.regs_out0 80 KS_bqNaDeq2 KS_bqNaDeq2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaDeq2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaDeq2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaDeq2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbqNaDeq2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbqNaDeq2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbqNaDeq2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbqNaDeq2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbqNaDeq2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbqNaDeq2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbqNaDeq2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbqNaDeq2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbqNaDeq2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq2.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbqNaDeq2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDeq2.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbqNaDeq2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K37l K37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaDgt0 := BndP_Eb_038S9.LibSegEb_bqNaDgt0.
Definition KS_bqNaDgt0 : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaDgt0.regs0 PbqNaDgt0.regs_out0).
Lemma KS_bqNaDgt0_ok : BG.kept_ok 80 PbqNaDgt0.regs0 PbqNaDgt0.regs_out0 KS_bqNaDgt0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaDgt0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 10%nat) + 48) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  L5.u32_at RSEGS M ((V 10%nat) + 48) (V 43%nat) -> 1 <= (V 43%nat) <= 1024 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> aligned (V 38%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 24) / 8) + 2147450880) 3 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u32_at RSEGS M ((V 39%nat) - 24) 0 -> L5.u64_at RSEGS M ((V 39%nat) - 16) (V 46%nat) -> 0 <= (V 46%nat) <= 16777216 ->
  L5.u64_at RSEGS M ((V 39%nat) - 8) ((V 46%nat) + (V 52%nat)) -> 1 <= (V 52%nat) <= 18446744073692774399 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= bv_unsigned a < ((V 10%nat) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= i < ((V 10%nat) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabb70 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_bqNaDgt0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 703784
        /\ getr R' (reg 10) = Z_to_bv 64 (V 12%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 8
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 10%nat) + 24)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 10%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880)
        /\ L5.u32_at RSEGS M' ((V 10%nat) + 48) ((V 43%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 703228
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 82866
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.defined M' ((V 47%nat) + 24) 104
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G11 G12 G19 G21 G25 K0 K1 K2 pvzI14 K4 K5 pvzI15 K7 K8 K9 K10 K11 K12 K13 pvzI16 K15 K16 K17 K18 K19 K20 K21 K22 pvzI17 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 pvzI18 K35 K36 pvzI19 K38 K39 pvzI20 pvzI21 K42 K43 pvzI22 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 pvzI23 K56 pvzI24.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV47l; move HV47l before pvzI9; pose proof (proj2 pvzI9) as HV47r; move HV47r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV48l; move HV48l before pvzI10; pose proof (proj2 pvzI10) as HV48r; move HV48r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV52l; move HV52l before pvzI11; pose proof (proj2 pvzI11) as HV52r; move HV52r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV56l; move HV56l before pvzI12; pose proof (proj2 pvzI12) as HV56r; move HV56r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV57l; move HV57l before pvzI13; pose proof (proj2 pvzI13) as HV57r; move HV57r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K6l; move K6l before pvzI15; pose proof (proj2 pvzI15) as K6r; move K6r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K14l; move K14l before pvzI16; pose proof (proj2 pvzI16) as K14r; move K14r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K23l; move K23l before pvzI17; pose proof (proj2 pvzI17) as K23r; move K23r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K34l; move K34l before pvzI18; pose proof (proj2 pvzI18) as K34r; move K34r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K37l; move K37l before pvzI19; pose proof (proj2 pvzI19) as K37r; move K37r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K40l; move K40l before pvzI20; pose proof (proj2 pvzI20) as K40r; move K40r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K41l; move K41l before pvzI21; pose proof (proj2 pvzI21) as K41r; move K41r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K44l; move K44l before pvzI22; pose proof (proj2 pvzI22) as K44r; move K44r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K55l; move K55l before pvzI23; pose proof (proj2 pvzI23) as K55r; move K55r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K57l; move K57l before pvzI24; pose proof (proj2 pvzI24) as K57r; move K57r before pvzI24; clear pvzI24.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 52%nat => Z_to_bv 64 vz_52 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | 43%nat => vz_43 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 52%nat => vz_52 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbqNaDgt0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaDgt0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaDgt0.kn0).
  { unfold know_ok, PbqNaDgt0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear; lia | exact K42]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r HV39l HV39r K41l K41r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV46l HV46r K55l K55r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K55l K55r) | exact (conj K55l K55r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV46l HV46r K55l K55r HV52l HV52r K57l K57r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K57l K57r) | exact (conj K57l K57r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaDgt0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaDgt0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> ~ ((vz_10 + 48) <= bv_unsigned a < (vz_10 + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbqNaDgt0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K23l K23r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaDgt0.ps0) with 0xafda8 in Hms. change (SR.ps_regs PbqNaDgt0.ps0) with (map (fun i => (i, nth i PbqNaDgt0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaDgt0.ps0) with PbqNaDgt0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaDgt0.regs0 PbqNaDgt0.regs_out0 80 KS_bqNaDgt0 KS_bqNaDgt0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaDgt0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaDgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaDgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaDgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbqNaDgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbqNaDgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbqNaDgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbqNaDgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbqNaDgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbqNaDgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbqNaDgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbqNaDgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbqNaDgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbqNaDgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt0.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbqNaDgt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K37l K37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaDgt2 := BndP_Eb_038S9.LibSegEb_bqNaDgt2.
Definition KS_bqNaDgt2 : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaDgt2.regs0 PbqNaDgt2.regs_out0).
Lemma KS_bqNaDgt2_ok : BG.kept_ok 80 PbqNaDgt2.regs0 PbqNaDgt2.regs_out0 KS_bqNaDgt2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaDgt2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 52%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 10%nat) + 48) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  L5.u32_at RSEGS M ((V 10%nat) + 48) (V 43%nat) -> 1 <= (V 43%nat) <= 1024 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> aligned (V 38%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 24) / 8) + 2147450880) 3 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u32_at RSEGS M ((V 39%nat) - 24) 2 -> L5.u64_at RSEGS M ((V 39%nat) - 16) (V 46%nat) -> 0 <= (V 46%nat) <= 16777216 ->
  L5.u64_at RSEGS M ((V 39%nat) - 8) ((V 46%nat) + (V 52%nat)) -> 1 <= (V 52%nat) <= 18446744073692774399 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= bv_unsigned a < ((V 10%nat) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= i < ((V 10%nat) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabb70 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_bqNaDgt2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 703784
        /\ getr R' (reg 10) = Z_to_bv 64 (V 12%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 8
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 10%nat) + 24)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 10%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880)
        /\ L5.u32_at RSEGS M' ((V 10%nat) + 48) ((V 43%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 703228
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 82866
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.defined M' ((V 47%nat) + 24) 104
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G11 G12 G19 G21 G25 K0 K1 K2 pvzI14 K4 K5 pvzI15 K7 K8 K9 K10 K11 K12 K13 pvzI16 K15 K16 K17 K18 K19 K20 K21 K22 pvzI17 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 pvzI18 K35 K36 pvzI19 K38 K39 pvzI20 pvzI21 K42 K43 pvzI22 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 pvzI23 K56 pvzI24.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV46l; move HV46l before pvzI8; pose proof (proj2 pvzI8) as HV46r; move HV46r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV47l; move HV47l before pvzI9; pose proof (proj2 pvzI9) as HV47r; move HV47r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV48l; move HV48l before pvzI10; pose proof (proj2 pvzI10) as HV48r; move HV48r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV52l; move HV52l before pvzI11; pose proof (proj2 pvzI11) as HV52r; move HV52r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV56l; move HV56l before pvzI12; pose proof (proj2 pvzI12) as HV56r; move HV56r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV57l; move HV57l before pvzI13; pose proof (proj2 pvzI13) as HV57r; move HV57r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K6l; move K6l before pvzI15; pose proof (proj2 pvzI15) as K6r; move K6r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K14l; move K14l before pvzI16; pose proof (proj2 pvzI16) as K14r; move K14r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K23l; move K23l before pvzI17; pose proof (proj2 pvzI17) as K23r; move K23r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K34l; move K34l before pvzI18; pose proof (proj2 pvzI18) as K34r; move K34r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K37l; move K37l before pvzI19; pose proof (proj2 pvzI19) as K37r; move K37r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K40l; move K40l before pvzI20; pose proof (proj2 pvzI20) as K40r; move K40r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K41l; move K41l before pvzI21; pose proof (proj2 pvzI21) as K41r; move K41r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K44l; move K44l before pvzI22; pose proof (proj2 pvzI22) as K44r; move K44r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K55l; move K55l before pvzI23; pose proof (proj2 pvzI23) as K55r; move K55r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K57l; move K57l before pvzI24; pose proof (proj2 pvzI24) as K57r; move K57r before pvzI24; clear pvzI24.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_52 := V 52%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 52%nat => Z_to_bv 64 vz_52 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | 43%nat => vz_43 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 52%nat => vz_52 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbqNaDgt2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaDgt2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaDgt2.kn0).
  { unfold know_ok, PbqNaDgt2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear; lia | exact K42]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r HV39l HV39r K41l K41r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV46l HV46r K55l K55r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K55l K55r) | exact (conj K55l K55r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV46l HV46r K55l K55r HV52l HV52r K57l K57r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV52l HV52r K57l K57r) | exact (conj K57l K57r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaDgt2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaDgt2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> ~ ((vz_10 + 48) <= bv_unsigned a < (vz_10 + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbqNaDgt2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K23l K23r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaDgt2.ps0) with 0xafda8 in Hms. change (SR.ps_regs PbqNaDgt2.ps0) with (map (fun i => (i, nth i PbqNaDgt2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaDgt2.ps0) with PbqNaDgt2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaDgt2.regs0 PbqNaDgt2.regs_out0 80 KS_bqNaDgt2 KS_bqNaDgt2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaDgt2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaDgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaDgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaDgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbqNaDgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbqNaDgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbqNaDgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbqNaDgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbqNaDgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbqNaDgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbqNaDgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbqNaDgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbqNaDgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt2.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbqNaDgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgt2.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbqNaDgt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K37l K37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaDgth0 := BndP_Eb_038S9.LibSegEb_bqNaDgth0.
Definition KS_bqNaDgth0 : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaDgth0.regs0 PbqNaDgth0.regs_out0).
Lemma KS_bqNaDgth0_ok : BG.kept_ok 80 PbqNaDgth0.regs0 PbqNaDgth0.regs_out0 KS_bqNaDgth0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaDgth0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 10%nat) + 48) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  L5.u32_at RSEGS M ((V 10%nat) + 48) (V 43%nat) -> 1 <= (V 43%nat) <= 1024 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> aligned (V 38%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 24) / 8) + 2147450880) 3 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u32_at RSEGS M ((V 39%nat) - 24) 0 -> L5.u64_at RSEGS M ((V 39%nat) - 16) (V 46%nat) -> 0 <= (V 46%nat) <= 16777216 ->
  L5.u64_at RSEGS M ((V 39%nat) - 8) (V 42%nat) -> 18446744073692774400 <= (V 42%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= bv_unsigned a < ((V 10%nat) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= i < ((V 10%nat) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabb70 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_bqNaDgth0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 703784
        /\ getr R' (reg 10) = Z_to_bv 64 (V 12%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 8
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 10%nat) + 24)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 10%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880)
        /\ L5.u32_at RSEGS M' ((V 10%nat) + 48) ((V 43%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 703228
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 82866
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.defined M' ((V 47%nat) + 24) 104
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G11 G12 G19 G21 G25 K0 K1 K2 pvzI14 K4 K5 pvzI15 K7 K8 K9 K10 K11 K12 K13 pvzI16 K15 K16 K17 K18 K19 K20 K21 K22 pvzI17 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 pvzI18 K35 K36 pvzI19 K38 K39 pvzI20 pvzI21 K42 K43 pvzI22 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 pvzI23 K56 pvzI24.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV42l; move HV42l before pvzI7; pose proof (proj2 pvzI7) as HV42r; move HV42r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV56l; move HV56l before pvzI12; pose proof (proj2 pvzI12) as HV56r; move HV56r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV57l; move HV57l before pvzI13; pose proof (proj2 pvzI13) as HV57r; move HV57r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K6l; move K6l before pvzI15; pose proof (proj2 pvzI15) as K6r; move K6r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K14l; move K14l before pvzI16; pose proof (proj2 pvzI16) as K14r; move K14r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K23l; move K23l before pvzI17; pose proof (proj2 pvzI17) as K23r; move K23r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K34l; move K34l before pvzI18; pose proof (proj2 pvzI18) as K34r; move K34r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K37l; move K37l before pvzI19; pose proof (proj2 pvzI19) as K37r; move K37r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K40l; move K40l before pvzI20; pose proof (proj2 pvzI20) as K40r; move K40r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K41l; move K41l before pvzI21; pose proof (proj2 pvzI21) as K41r; move K41r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K44l; move K44l before pvzI22; pose proof (proj2 pvzI22) as K44r; move K44r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K55l; move K55l before pvzI23; pose proof (proj2 pvzI23) as K55r; move K55r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K57l; move K57l before pvzI24; pose proof (proj2 pvzI24) as K57r; move K57r before pvzI24; clear pvzI24.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbqNaDgth0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaDgth0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaDgth0.kn0).
  { unfold know_ok, PbqNaDgth0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear; lia | exact K42]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r HV39l HV39r K41l K41r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV46l HV46r K55l K55r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K55l K55r) | exact (conj K55l K55r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV42l HV42r K57l K57r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K57l K57r) | exact (conj K57l K57r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaDgth0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaDgth0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> ~ ((vz_10 + 48) <= bv_unsigned a < (vz_10 + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbqNaDgth0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K23l K23r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaDgth0.ps0) with 0xafda8 in Hms. change (SR.ps_regs PbqNaDgth0.ps0) with (map (fun i => (i, nth i PbqNaDgth0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaDgth0.ps0) with PbqNaDgth0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaDgth0.regs0 PbqNaDgth0.regs_out0 80 KS_bqNaDgth0 KS_bqNaDgth0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaDgth0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaDgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaDgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaDgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbqNaDgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbqNaDgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbqNaDgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbqNaDgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbqNaDgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbqNaDgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbqNaDgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbqNaDgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbqNaDgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbqNaDgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth0.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbqNaDgth0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K37l K37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaDgth2 := BndP_Eb_038S9.LibSegEb_bqNaDgth2.
Definition KS_bqNaDgth2 : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaDgth2.regs0 PbqNaDgth2.regs_out0).
Lemma KS_bqNaDgth2_ok : BG.kept_ok 80 PbqNaDgth2.regs0 PbqNaDgth2.regs_out0 KS_bqNaDgth2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaDgth2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 10%nat) + 48) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  L5.u32_at RSEGS M ((V 10%nat) + 48) (V 43%nat) -> 1 <= (V 43%nat) <= 1024 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> aligned (V 38%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 24) / 8) + 2147450880) 3 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u32_at RSEGS M ((V 39%nat) - 24) 2 -> L5.u64_at RSEGS M ((V 39%nat) - 16) (V 46%nat) -> 0 <= (V 46%nat) <= 16777216 ->
  L5.u64_at RSEGS M ((V 39%nat) - 8) (V 42%nat) -> 18446744073692774400 <= (V 42%nat) <= 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= bv_unsigned a < ((V 10%nat) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= i < ((V 10%nat) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabb70 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_bqNaDgth2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 703784
        /\ getr R' (reg 10) = Z_to_bv 64 (V 12%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 8
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 10%nat) + 24)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 10%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880)
        /\ L5.u32_at RSEGS M' ((V 10%nat) + 48) ((V 43%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 703228
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 82866
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.defined M' ((V 47%nat) + 24) 104
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G11 G12 G19 G21 G25 K0 K1 K2 pvzI14 K4 K5 pvzI15 K7 K8 K9 K10 K11 K12 K13 pvzI16 K15 K16 K17 K18 K19 K20 K21 K22 pvzI17 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 pvzI18 K35 K36 pvzI19 K38 K39 pvzI20 pvzI21 K42 K43 pvzI22 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 pvzI23 K56 pvzI24.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV42l; move HV42l before pvzI7; pose proof (proj2 pvzI7) as HV42r; move HV42r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV56l; move HV56l before pvzI12; pose proof (proj2 pvzI12) as HV56r; move HV56r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV57l; move HV57l before pvzI13; pose proof (proj2 pvzI13) as HV57r; move HV57r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K6l; move K6l before pvzI15; pose proof (proj2 pvzI15) as K6r; move K6r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K14l; move K14l before pvzI16; pose proof (proj2 pvzI16) as K14r; move K14r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K23l; move K23l before pvzI17; pose proof (proj2 pvzI17) as K23r; move K23r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K34l; move K34l before pvzI18; pose proof (proj2 pvzI18) as K34r; move K34r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K37l; move K37l before pvzI19; pose proof (proj2 pvzI19) as K37r; move K37r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K40l; move K40l before pvzI20; pose proof (proj2 pvzI20) as K40r; move K40r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K41l; move K41l before pvzI21; pose proof (proj2 pvzI21) as K41r; move K41r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K44l; move K44l before pvzI22; pose proof (proj2 pvzI22) as K44r; move K44r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K55l; move K55l before pvzI23; pose proof (proj2 pvzI23) as K55r; move K55r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K57l; move K57l before pvzI24; pose proof (proj2 pvzI24) as K57r; move K57r before pvzI24; clear pvzI24.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbqNaDgth2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaDgth2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaDgth2.kn0).
  { unfold know_ok, PbqNaDgth2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear; lia | exact K42]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r HV39l HV39r K41l K41r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV46l HV46r K55l K55r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K55l K55r) | exact (conj K55l K55r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV42l HV42r K57l K57r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K57l K57r) | exact (conj K57l K57r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaDgth2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaDgth2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> ~ ((vz_10 + 48) <= bv_unsigned a < (vz_10 + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbqNaDgth2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K23l K23r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaDgth2.ps0) with 0xafda8 in Hms. change (SR.ps_regs PbqNaDgth2.ps0) with (map (fun i => (i, nth i PbqNaDgth2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaDgth2.ps0) with PbqNaDgth2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaDgth2.regs0 PbqNaDgth2.regs_out0 80 KS_bqNaDgth2 KS_bqNaDgth2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaDgth2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaDgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaDgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaDgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbqNaDgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbqNaDgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbqNaDgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbqNaDgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbqNaDgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbqNaDgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbqNaDgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbqNaDgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbqNaDgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth2.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbqNaDgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDgth2.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbqNaDgth2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K37l K37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaDi1 := BndP_Eb_038S9.LibSegEb_bqNaDi1.
Definition KS_bqNaDi1 : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaDi1.regs0 PbqNaDi1.regs_out0).
Lemma KS_bqNaDi1_ok : BG.kept_ok 80 PbqNaDi1.regs0 PbqNaDi1.regs_out0 KS_bqNaDi1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaDi1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 10%nat) + 48) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  L5.u32_at RSEGS M ((V 10%nat) + 48) (V 43%nat) -> 1 <= (V 43%nat) <= 1024 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> aligned (V 38%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 24) / 8) + 2147450880) 3 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u32_at RSEGS M ((V 39%nat) - 24) 1 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= bv_unsigned a < ((V 10%nat) + 48) + 4) -> ~ (((V 2%nat) - 105) <= bv_unsigned a < ((V 2%nat) - 105) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= i < ((V 10%nat) + 48) + 4) -> ~ (((V 2%nat) - 105) <= i < ((V 2%nat) - 105) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabb70 M) (st fx' R' 0xb120c M')
        /\ (forall x, In x KS_bqNaDi1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 703704
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 105)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 10%nat) + 24)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 10%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 105) 93
        /\ L5.u32_at RSEGS M' ((V 10%nat) + 48) ((V 43%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 703228
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 82866
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.defined M' ((V 47%nat) + 24) 104
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G10 G11 G12 G19 G21 G25 K0 K1 K2 pvzI12 K4 K5 pvzI13 K7 K8 K9 K10 K11 K12 K13 pvzI14 K15 K16 K17 K18 K19 K20 K21 K22 pvzI15 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 pvzI16 K35 K36 pvzI17 K38 K39 pvzI18 pvzI19 K42 K43 pvzI20 K45 K46 K47 K48 K49 K50 K51 K52 K53.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV47l; move HV47l before pvzI8; pose proof (proj2 pvzI8) as HV47r; move HV47r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV56l; move HV56l before pvzI10; pose proof (proj2 pvzI10) as HV56r; move HV56r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV57l; move HV57l before pvzI11; pose proof (proj2 pvzI11) as HV57r; move HV57r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K3l; move K3l before pvzI12; pose proof (proj2 pvzI12) as K3r; move K3r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K6l; move K6l before pvzI13; pose proof (proj2 pvzI13) as K6r; move K6r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K14l; move K14l before pvzI14; pose proof (proj2 pvzI14) as K14r; move K14r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K23l; move K23l before pvzI15; pose proof (proj2 pvzI15) as K23r; move K23r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K34l; move K34l before pvzI16; pose proof (proj2 pvzI16) as K34r; move K34r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K37l; move K37l before pvzI17; pose proof (proj2 pvzI17) as K37r; move K37r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K40l; move K40l before pvzI18; pose proof (proj2 pvzI18) as K40r; move K40r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K41l; move K41l before pvzI19; pose proof (proj2 pvzI19) as K41r; move K41r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K44l; move K44l before pvzI20; pose proof (proj2 pvzI20) as K44r; move K44r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | 43%nat => vz_43 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbqNaDi1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaDi1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaDi1.kn0).
  { unfold know_ok, PbqNaDi1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear; lia | exact K42]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r HV39l HV39r K41l K41r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K53]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaDi1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaDi1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> ~ ((vz_10 + 48) <= bv_unsigned a < (vz_10 + 48) + 4) -> ~ ((vz_2 - 105) <= bv_unsigned a < (vz_2 - 105) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4. apply Hfr. unfold PbqNaDi1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K23l K23r Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn4; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaDi1.ps0) with 0xb120c in Hms. change (SR.ps_regs PbqNaDi1.ps0) with (map (fun i => (i, nth i PbqNaDi1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaDi1.ps0) with PbqNaDi1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaDi1.regs0 PbqNaDi1.regs_out0 80 KS_bqNaDi1 KS_bqNaDi1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaDi1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaDi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaDi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaDi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi1.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbqNaDi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi1.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbqNaDi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi1.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbqNaDi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi1.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbqNaDi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbqNaDi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbqNaDi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbqNaDi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbqNaDi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbqNaDi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbqNaDi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi1.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbqNaDi1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K37l K37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaDi3 := BndP_Eb_038S9.LibSegEb_bqNaDi3.
Definition KS_bqNaDi3 : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaDi3.regs0 PbqNaDi3.regs_out0).
Lemma KS_bqNaDi3_ok : BG.kept_ok 80 PbqNaDi3.regs0 PbqNaDi3.regs_out0 KS_bqNaDi3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaDi3_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 10%nat) + 48) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  L5.u32_at RSEGS M ((V 10%nat) + 48) (V 43%nat) -> 1 <= (V 43%nat) <= 1024 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> aligned (V 38%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 24) / 8) + 2147450880) 3 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u32_at RSEGS M ((V 39%nat) - 24) 3 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= bv_unsigned a < ((V 10%nat) + 48) + 4) -> ~ (((V 2%nat) - 105) <= bv_unsigned a < ((V 2%nat) - 105) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= i < ((V 10%nat) + 48) + 4) -> ~ (((V 2%nat) - 105) <= i < ((V 2%nat) - 105) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabb70 M) (st fx' R' 0xb120c M')
        /\ (forall x, In x KS_bqNaDi3 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 703704
        /\ getr R' (reg 10) = Z_to_bv 64 (V 41%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 2%nat) - 105)
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 10%nat) + 24)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 10%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880)
        /\ L5.u8_at RSEGS M' ((V 2%nat) - 105) 93
        /\ L5.u32_at RSEGS M' ((V 10%nat) + 48) ((V 43%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 703228
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 82866
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.defined M' ((V 47%nat) + 24) 104
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 G2 G8 G9 G10 G11 G12 G19 G21 G25 K0 K1 K2 pvzI12 K4 K5 pvzI13 K7 K8 K9 K10 K11 K12 K13 pvzI14 K15 K16 K17 K18 K19 K20 K21 K22 pvzI15 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 pvzI16 K35 K36 pvzI17 K38 K39 pvzI18 pvzI19 K42 K43 pvzI20 K45 K46 K47 K48 K49 K50 K51 K52 K53.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV43l; move HV43l before pvzI7; pose proof (proj2 pvzI7) as HV43r; move HV43r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV47l; move HV47l before pvzI8; pose proof (proj2 pvzI8) as HV47r; move HV47r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV56l; move HV56l before pvzI10; pose proof (proj2 pvzI10) as HV56r; move HV56r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV57l; move HV57l before pvzI11; pose proof (proj2 pvzI11) as HV57r; move HV57r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K3l; move K3l before pvzI12; pose proof (proj2 pvzI12) as K3r; move K3r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K6l; move K6l before pvzI13; pose proof (proj2 pvzI13) as K6r; move K6r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K14l; move K14l before pvzI14; pose proof (proj2 pvzI14) as K14r; move K14r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K23l; move K23l before pvzI15; pose proof (proj2 pvzI15) as K23r; move K23r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K34l; move K34l before pvzI16; pose proof (proj2 pvzI16) as K34r; move K34r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K37l; move K37l before pvzI17; pose proof (proj2 pvzI17) as K37r; move K37r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K40l; move K40l before pvzI18; pose proof (proj2 pvzI18) as K40r; move K40r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K41l; move K41l before pvzI19; pose proof (proj2 pvzI19) as K41r; move K41r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K44l; move K44l before pvzI20; pose proof (proj2 pvzI20) as K44r; move K44r before pvzI20; clear pvzI20.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 43%nat => Z_to_bv 64 vz_43 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | 43%nat => vz_43 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbqNaDi3.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaDi3.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaDi3.kn0).
  { unfold know_ok, PbqNaDi3.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear; lia | exact K42]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r HV39l HV39r K41l K41r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K53]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaDi3.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaDi3.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> ~ ((vz_10 + 48) <= bv_unsigned a < (vz_10 + 48) + 4) -> ~ ((vz_2 - 105) <= bv_unsigned a < (vz_2 - 105) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4. apply Hfr. unfold PbqNaDi3.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K23l K23r Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn4; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaDi3.ps0) with 0xb120c in Hms. change (SR.ps_regs PbqNaDi3.ps0) with (map (fun i => (i, nth i PbqNaDi3.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaDi3.ps0) with PbqNaDi3.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaDi3.regs0 PbqNaDi3.regs_out0 80 KS_bqNaDi3 KS_bqNaDi3_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaDi3.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaDi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi3.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaDi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi3.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaDi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi3.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbqNaDi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi3.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbqNaDi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi3.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbqNaDi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi3.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbqNaDi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi3.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbqNaDi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi3.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbqNaDi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi3.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbqNaDi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi3.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbqNaDi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi3.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbqNaDi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi3.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbqNaDi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDi3.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbqNaDi3.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K37l K37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaDlt0 := BndP_Eb_038S9.LibSegEb_bqNaDlt0.
Definition KS_bqNaDlt0 : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaDlt0.regs0 PbqNaDlt0.regs_out0).
Lemma KS_bqNaDlt0_ok : BG.kept_ok 80 PbqNaDlt0.regs0 PbqNaDlt0.regs_out0 KS_bqNaDlt0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaDlt0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 10%nat) + 48) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  L5.u32_at RSEGS M ((V 10%nat) + 48) (V 43%nat) -> 1 <= (V 43%nat) <= 1024 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> aligned (V 38%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 24) / 8) + 2147450880) 3 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u32_at RSEGS M ((V 39%nat) - 24) 0 -> L5.u64_at RSEGS M ((V 39%nat) - 16) (V 46%nat) -> 0 <= (V 46%nat) <= 16777216 ->
  L5.u64_at RSEGS M ((V 39%nat) - 8) (V 42%nat) -> 0 <= (V 42%nat) <= 16777215 -> 1 <= ((V 46%nat) - (V 42%nat)) <= 16777216 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= bv_unsigned a < ((V 10%nat) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= i < ((V 10%nat) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabb70 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_bqNaDlt0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 703784
        /\ getr R' (reg 10) = Z_to_bv 64 (V 12%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 9
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 10%nat) + 24)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 10%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880)
        /\ L5.u32_at RSEGS M' ((V 10%nat) + 48) ((V 43%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 703228
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 82866
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.defined M' ((V 47%nat) + 24) 104
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G11 G12 G19 G21 G25 K0 K1 K2 pvzI14 K4 K5 pvzI15 K7 K8 K9 K10 K11 K12 K13 pvzI16 K15 K16 K17 K18 K19 K20 K21 K22 pvzI17 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 pvzI18 K35 K36 pvzI19 K38 K39 pvzI20 pvzI21 K42 K43 pvzI22 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 pvzI23 K56 pvzI24 pvzI25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV42l; move HV42l before pvzI7; pose proof (proj2 pvzI7) as HV42r; move HV42r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV56l; move HV56l before pvzI12; pose proof (proj2 pvzI12) as HV56r; move HV56r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV57l; move HV57l before pvzI13; pose proof (proj2 pvzI13) as HV57r; move HV57r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K6l; move K6l before pvzI15; pose proof (proj2 pvzI15) as K6r; move K6r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K14l; move K14l before pvzI16; pose proof (proj2 pvzI16) as K14r; move K14r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K23l; move K23l before pvzI17; pose proof (proj2 pvzI17) as K23r; move K23r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K34l; move K34l before pvzI18; pose proof (proj2 pvzI18) as K34r; move K34r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K37l; move K37l before pvzI19; pose proof (proj2 pvzI19) as K37r; move K37r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K40l; move K40l before pvzI20; pose proof (proj2 pvzI20) as K40r; move K40r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K41l; move K41l before pvzI21; pose proof (proj2 pvzI21) as K41r; move K41r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K44l; move K44l before pvzI22; pose proof (proj2 pvzI22) as K44r; move K44r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K55l; move K55l before pvzI23; pose proof (proj2 pvzI23) as K55r; move K55r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K57l; move K57l before pvzI24; pose proof (proj2 pvzI24) as K57r; move K57r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K58l; move K58l before pvzI25; pose proof (proj2 pvzI25) as K58r; move K58r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbqNaDlt0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaDlt0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaDlt0.kn0).
  { unfold know_ok, PbqNaDlt0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear; lia | exact K42]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r HV39l HV39r K41l K41r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV46l HV46r K55l K55r K58l K58r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K55l K55r K58l K58r) | exact (conj K55l K55r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV42l HV42r K57l K57r K58l K58r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K57l K57r K58l K58r) | exact (conj K57l K57r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K57l K57r K58l K58r HV46l HV46r K55l K55r) | exact (conj K58l K58r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaDlt0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaDlt0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> ~ ((vz_10 + 48) <= bv_unsigned a < (vz_10 + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbqNaDlt0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K23l K23r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaDlt0.ps0) with 0xafda8 in Hms. change (SR.ps_regs PbqNaDlt0.ps0) with (map (fun i => (i, nth i PbqNaDlt0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaDlt0.ps0) with PbqNaDlt0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaDlt0.regs0 PbqNaDlt0.regs_out0 80 KS_bqNaDlt0 KS_bqNaDlt0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaDlt0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaDlt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaDlt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaDlt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt0.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbqNaDlt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt0.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbqNaDlt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt0.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbqNaDlt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt0.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbqNaDlt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbqNaDlt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbqNaDlt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbqNaDlt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbqNaDlt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbqNaDlt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbqNaDlt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt0.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbqNaDlt0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K37l K37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaDlt2 := BndP_Eb_038S9.LibSegEb_bqNaDlt2.
Definition KS_bqNaDlt2 : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaDlt2.regs0 PbqNaDlt2.regs_out0).
Lemma KS_bqNaDlt2_ok : BG.kept_ok 80 PbqNaDlt2.regs0 PbqNaDlt2.regs_out0 KS_bqNaDlt2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaDlt2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 41%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 43%nat) < 2 ^ 64 -> 0 <= (V 46%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 ->
  (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) ->
  ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 ->
  aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 ->
  (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 10%nat) + 48) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 8) (V 41%nat) -> 4096 <= (V 41%nat) <= 140737488355304 -> aligned (V 41%nat) 8 ->
  L5.u32_at RSEGS M ((V 10%nat) + 48) (V 43%nat) -> 1 <= (V 43%nat) <= 1024 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> aligned (V 38%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 24) / 8) + 2147450880) 3 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 39%nat) - 24) / 8) + 2147450880)) -> L5.u32_at RSEGS M ((V 39%nat) - 24) 2 -> L5.u64_at RSEGS M ((V 39%nat) - 16) (V 46%nat) -> 0 <= (V 46%nat) <= 16777216 ->
  L5.u64_at RSEGS M ((V 39%nat) - 8) (V 42%nat) -> 0 <= (V 42%nat) <= 16777215 -> 1 <= ((V 46%nat) - (V 42%nat)) <= 16777216 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 120) <= bv_unsigned a < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= bv_unsigned a < ((V 10%nat) + 48) + 4) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 120) <= i < ((V 2%nat) - 120) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 12) -> ~ (((V 10%nat) + 48) <= i < ((V 10%nat) + 48) + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabb70 M) (st fx' R' 0xafda8 M')
        /\ (forall x, In x KS_bqNaDlt2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 703784
        /\ getr R' (reg 10) = Z_to_bv 64 (V 12%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 9
        /\ getr R' (reg 12) = Z_to_bv 64 0
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 (V 43%nat)
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 18) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 ((V 10%nat) + 24)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 10%nat) + 32)
        /\ getr R' (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880)
        /\ getr R' (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880)
        /\ L5.u32_at RSEGS M' ((V 10%nat) + 48) ((V 43%nat) - 1)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 120) (V 47%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 703228
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 82866
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.defined M' ((V 47%nat) + 24) 104
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 G2 G8 G9 G10 G11 G12 G19 G21 G25 K0 K1 K2 pvzI14 K4 K5 pvzI15 K7 K8 K9 K10 K11 K12 K13 pvzI16 K15 K16 K17 K18 K19 K20 K21 K22 pvzI17 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 pvzI18 K35 K36 pvzI19 K38 K39 pvzI20 pvzI21 K42 K43 pvzI22 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 pvzI23 K56 pvzI24 pvzI25.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV41l; move HV41l before pvzI6; pose proof (proj2 pvzI6) as HV41r; move HV41r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV42l; move HV42l before pvzI7; pose proof (proj2 pvzI7) as HV42r; move HV42r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV43l; move HV43l before pvzI8; pose proof (proj2 pvzI8) as HV43r; move HV43r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV46l; move HV46l before pvzI9; pose proof (proj2 pvzI9) as HV46r; move HV46r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV47l; move HV47l before pvzI10; pose proof (proj2 pvzI10) as HV47r; move HV47r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV48l; move HV48l before pvzI11; pose proof (proj2 pvzI11) as HV48r; move HV48r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV56l; move HV56l before pvzI12; pose proof (proj2 pvzI12) as HV56r; move HV56r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV57l; move HV57l before pvzI13; pose proof (proj2 pvzI13) as HV57r; move HV57r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K3l; move K3l before pvzI14; pose proof (proj2 pvzI14) as K3r; move K3r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K6l; move K6l before pvzI15; pose proof (proj2 pvzI15) as K6r; move K6r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K14l; move K14l before pvzI16; pose proof (proj2 pvzI16) as K14r; move K14r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K23l; move K23l before pvzI17; pose proof (proj2 pvzI17) as K23r; move K23r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K34l; move K34l before pvzI18; pose proof (proj2 pvzI18) as K34r; move K34r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K37l; move K37l before pvzI19; pose proof (proj2 pvzI19) as K37r; move K37r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as K40l; move K40l before pvzI20; pose proof (proj2 pvzI20) as K40r; move K40r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as K41l; move K41l before pvzI21; pose proof (proj2 pvzI21) as K41r; move K41r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K44l; move K44l before pvzI22; pose proof (proj2 pvzI22) as K44r; move K44r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K55l; move K55l before pvzI23; pose proof (proj2 pvzI23) as K55r; move K55r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K57l; move K57l before pvzI24; pose proof (proj2 pvzI24) as K57r; move K57r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K58l; move K58l before pvzI25; pose proof (proj2 pvzI25) as K58r; move K58r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_41 := V 41%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_43 := V 43%nat) in *. set (vz_46 := V 46%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 41%nat => Z_to_bv 64 vz_41 | 42%nat => Z_to_bv 64 vz_42 | 43%nat => Z_to_bv 64 vz_43 | 46%nat => Z_to_bv 64 vz_46 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 38%nat => vz_38 | 39%nat => vz_39 | 41%nat => vz_41 | 42%nat => vz_42 | 43%nat => vz_43 | 46%nat => vz_46 | 47%nat => vz_47 | 48%nat => vz_48 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbqNaDlt2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaDlt2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaDlt2.kn0).
  { unfold know_ok, PbqNaDlt2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | exact (conj K14l K14r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | clear - HV48l HV48r K14l K14r; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | exact (conj K23l K23r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | clear; lia | exact K24]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K25; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K28; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | exact (conj K34l K34r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV41l HV41r K34l K34r) | clear; lia | exact K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV43l HV43r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear - HV10l HV10r K23l K23r; lia | clear - HV10l HV10r K23l K23r; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | clear; lia | exact K42]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r) | clear; lia | exact K43]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K40l K40r K44l K44r HV39l HV39r K41l K41r) | exact (conj K44l K44r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K23l K23r) | evalEk ZA ltac:(clear) | generalize K49; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K50; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K14l K14r) | evalEk ZA ltac:(clear) | generalize K51; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV46l HV46r K55l K55r K58l K58r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K54]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV46l HV46r K55l K55r K58l K58r) | exact (conj K55l K55r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV39l HV39r K41l K41r K44l K44r) | evalEk ZA ltac:(clear - HV42l HV42r K57l K57r K58l K58r) | clear - HV39l HV39r K41l K41r K44l K44r; lia | clear - HV39l HV39r K41l K41r K44l K44r; lia | exactA K56]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K57l K57r K58l K58r) | exact (conj K57l K57r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K57l K57r K58l K58r HV46l HV46r K55l K55r) | exact (conj K58l K58r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaDlt2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaDlt2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 120) <= bv_unsigned a < (vz_2 - 120) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 12) -> ~ ((vz_10 + 48) <= bv_unsigned a < (vz_10 + 48) + 4) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbqNaDlt2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K23l K23r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaDlt2.ps0) with 0xafda8 in Hms. change (SR.ps_regs PbqNaDlt2.ps0) with (map (fun i => (i, nth i PbqNaDlt2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaDlt2.ps0) with PbqNaDlt2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaDlt2.regs0 PbqNaDlt2.regs_out0 80 KS_bqNaDlt2 KS_bqNaDlt2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaDlt2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaDlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaDlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaDlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbqNaDlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt2.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbqNaDlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt2.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbqNaDlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt2.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbqNaDlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt2.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbqNaDlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbqNaDlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbqNaDlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt2.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbqNaDlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbqNaDlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt2.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbqNaDlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaDlt2.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbqNaDlt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u32_of_KWord4a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K23l K23r) | evalEk' ZA Hag ltac:(clear - HV43l HV43r K37l K37r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaP := BndP_Eb_038S9.LibSegEb_bqNaP.
Definition KS_bqNaP : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaP.regs0 PbqNaP.regs_out0).
Lemma KS_bqNaP_ok : BG.kept_ok 80 PbqNaP.regs0 PbqNaP.regs_out0 KS_bqNaP = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaP_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 10%nat) + 24) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 10%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880) ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.writable RSEGS M ((V 2%nat) - 144) 16 -> (((V 2%nat) - 144) + 16 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 144)) ->
  4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 ->
  (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) ->
  (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) ->
  4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 ->
  L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 48) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> aligned (V 38%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 24) / 8) + 2147450880) 3 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 39%nat) - 24) / 8) + 2147450880)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabd2c M) (st fx' R' 0xb35e0 M')
        /\ (forall x, In x KS_bqNaP -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 703824
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 144)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 10%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 39%nat) - 24)
        /\ getr R' (reg 12) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 (((-1) * (V 38%nat)) + (V 39%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 24
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 39%nat) - 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 703824).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI11 K4 K5 K6 K7 pvzI12 K9 K10 K11 K12 K13 K14 pvzI13 K16 K17 K18 K19 K20 K21 K22 K23 pvzI14 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 pvzI15 pvzI16 K38 K39 pvzI17 K41 K42 K43 K44 K45 K46 K47 K48.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV56l; move HV56l before pvzI9; pose proof (proj2 pvzI9) as HV56r; move HV56r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV57l; move HV57l before pvzI10; pose proof (proj2 pvzI10) as HV57r; move HV57r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K8l; move K8l before pvzI12; pose proof (proj2 pvzI12) as K8r; move K8r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K15l; move K15l before pvzI13; pose proof (proj2 pvzI13) as K15r; move K15r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K24l; move K24l before pvzI14; pose proof (proj2 pvzI14) as K24r; move K24r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K36l; move K36l before pvzI15; pose proof (proj2 pvzI15) as K36r; move K36r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K37l; move K37l before pvzI16; pose proof (proj2 pvzI16) as K37r; move K37r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K40l; move K40l before pvzI17; pose proof (proj2 pvzI17) as K40r; move K40r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 38%nat => vz_38 | 39%nat => vz_39 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbqNaP.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaP.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaP.kn0).
  { unfold know_ok, PbqNaP.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K8l K8r; lia | clear - HV47l HV47r K8l K8r; lia | clear - HV47l HV47r K8l K8r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K8l K8r; lia | clear - HV47l HV47r K8l K8r; lia | clear - HV47l HV47r K8l K8r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K8l K8r; lia | clear - HV47l HV47r K8l K8r; lia | clear - HV47l HV47r K8l K8r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | clear - HV47l HV47r K8l K8r; lia | clear - HV47l HV47r K8l K8r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K15l K15r; lia | clear - HV48l HV48r K15l K15r; lia | clear - HV48l HV48r K15l K15r; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | clear; lia | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear - HV38l HV38r K36l K36r K40l K40r) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K36l K36r K40l K40r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K36l K36r K40l K40r) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K36l K36r K40l K40r HV39l HV39r K37l K37r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K37l K37r K40l K40r; lia | clear - HV39l HV39r K37l K37r K40l K40r; lia | clear - HV39l HV39r K37l K37r K40l K40r; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K37l K37r K40l K40r; lia | clear - HV39l HV39r K37l K37r K40l K40r; lia | clear - HV39l HV39r K37l K37r K40l K40r; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaP.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaP.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 144) <= bv_unsigned a < (vz_2 - 144) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbqNaP.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaP.ps0) with 0xb35e0 in Hms. change (SR.ps_regs PbqNaP.ps0) with (map (fun i => (i, nth i PbqNaP.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaP.ps0) with PbqNaP.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaP.regs0 PbqNaP.regs_out0 80 KS_bqNaP KS_bqNaP_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaP.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaP.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbqNaP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaP.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaP.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaP.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbqNaP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaP.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbqNaP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaP.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbqNaP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaP.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbqNaP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaP.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbqNaP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaP.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PbqNaP.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaPj := BndP_Eb_038S9.LibSegEb_bqNaPj.
Definition KS_bqNaPj : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaPj.regs0 PbqNaPj.regs_out0).
Lemma KS_bqNaPj_ok : BG.kept_ok 80 PbqNaPj.regs0 PbqNaPj.regs_out0 KS_bqNaPj = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaPj_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 10%nat) + 24) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 10%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880) ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> L5.writable RSEGS M ((V 2%nat) - 144) 16 -> (((V 2%nat) - 144) + 16 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 144)) ->
  4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 ->
  (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) ->
  (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) -> ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) ->
  4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 -> (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 ->
  L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) -> L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 ->
  L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 48) / 8) + 2147450880) 1 -> L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 39%nat) ->
  4096 <= (V 38%nat) <= 140737488355328 -> 4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> aligned (V 38%nat) 8 ->
  24 <= ((V 39%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 39%nat) - 24) 24 -> (2147446784 + 17592186048512 <= ((V 39%nat) - 24) \/ ((V 39%nat) - 24) + 24 <= 2147446784) -> L5KA.zeros_at M ((((V 39%nat) - 24) / 8) + 2147450880) 3 ->
  (((V 39%nat) - 24) + 24 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 39%nat) - 24)) -> (((V 39%nat) - 24) + 24 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 39%nat) - 24)) ->
  (((((V 39%nat) - 24) / 8) + 2147450880) + 3 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 39%nat) - 24) / 8) + 2147450880)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 144) <= bv_unsigned a < ((V 2%nat) - 144) + 16) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 144) <= i < ((V 2%nat) - 144) + 16) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabcd8 M) (st fx' R' 0xb35e0 M')
        /\ (forall x, In x KS_bqNaPj -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 703824
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 144)
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 10%nat) + 24)
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 39%nat) - 24)
        /\ getr R' (reg 12) = Z_to_bv 64 12297829382473034411
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 (((-1) * (V 38%nat)) + (V 39%nat))
        /\ getr R' (reg 15) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 16) = Z_to_bv 64 24
        /\ getr R' (reg 17) = Z_to_bv 64 ((V 39%nat) - 24)
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 136) 703824).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI11 K4 K5 K6 K7 pvzI12 K9 K10 K11 K12 K13 K14 pvzI13 K16 K17 K18 K19 K20 K21 K22 K23 pvzI14 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 pvzI15 pvzI16 K38 K39 pvzI17 K41 K42 K43 K44 K45 K46 K47 K48.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV39l; move HV39l before pvzI5; pose proof (proj2 pvzI5) as HV39r; move HV39r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV56l; move HV56l before pvzI9; pose proof (proj2 pvzI9) as HV56r; move HV56r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV57l; move HV57l before pvzI10; pose proof (proj2 pvzI10) as HV57r; move HV57r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K8l; move K8l before pvzI12; pose proof (proj2 pvzI12) as K8r; move K8r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K15l; move K15l before pvzI13; pose proof (proj2 pvzI13) as K15r; move K15r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K24l; move K24l before pvzI14; pose proof (proj2 pvzI14) as K24r; move K24r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K36l; move K36l before pvzI15; pose proof (proj2 pvzI15) as K36r; move K36r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K37l; move K37l before pvzI16; pose proof (proj2 pvzI16) as K37r; move K37r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K40l; move K40l before pvzI17; pose proof (proj2 pvzI17) as K40r; move K40r before pvzI17; clear pvzI17.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 38%nat => Z_to_bv 64 vz_38 | 39%nat => Z_to_bv 64 vz_39 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 38%nat => vz_38 | 39%nat => vz_39 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 58%nat. }
  assert (HR: regs_ok E PbqNaPj.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaPj.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaPj.kn0).
  { unfold know_ok, PbqNaPj.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | generalize K7; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K8l K8r; lia | clear - HV47l HV47r K8l K8r; lia | clear - HV47l HV47r K8l K8r; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K8l K8r; lia | clear - HV47l HV47r K8l K8r; lia | clear - HV47l HV47r K8l K8r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | generalize K12; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K8l K8r; lia | clear - HV47l HV47r K8l K8r; lia | clear - HV47l HV47r K8l K8r; lia | exactA K13]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | clear - HV47l HV47r K8l K8r; lia | clear - HV47l HV47r K8l K8r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | exact (conj K15l K15r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K15l K15r; lia | clear - HV48l HV48r K15l K15r; lia | clear - HV48l HV48r K15l K15r; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | evalEk ZA ltac:(clear) | generalize K22; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | exact (conj K24l K24r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | clear; lia | exact K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear - HV38l HV38r K36l K36r K40l K40r) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | clear - HV10l HV10r K24l K24r; lia | clear - HV10l HV10r K24l K24r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K36l K36r K40l K40r) | exact (conj K36l K36r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV38l HV38r K36l K36r K40l K40r) | clear; lia | exact K39]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K36l K36r K40l K40r HV39l HV39r K37l K37r) | exact (conj K40l K40r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K37l K37r K40l K40r; lia | clear - HV39l HV39r K37l K37r K40l K40r; lia | clear - HV39l HV39r K37l K37r K40l K40r; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | clear - HV39l HV39r K37l K37r K40l K40r; lia | clear - HV39l HV39r K37l K37r K40l K40r; lia | clear - HV39l HV39r K37l K37r K40l K40r; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | generalize K44; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K24l K24r) | evalEk ZA ltac:(clear) | generalize K45; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | generalize K46; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K15l K15r) | evalEk ZA ltac:(clear) | generalize K47; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV39l HV39r K37l K37r K40l K40r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K8l K8r) | evalEk ZA ltac:(clear) | generalize K48; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaPj.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaPj.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 144) <= bv_unsigned a < (vz_2 - 144) + 16) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbqNaPj.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaPj.ps0) with 0xb35e0 in Hms. change (SR.ps_regs PbqNaPj.ps0) with (map (fun i => (i, nth i PbqNaPj.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaPj.ps0) with PbqNaPj.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaPj.regs0 PbqNaPj.regs_out0 80 KS_bqNaPj KS_bqNaPj_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaPj.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaPj.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaPj.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbqNaPj.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaPj.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaPj.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaPj.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaPj.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaPj.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbqNaPj.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaPj.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbqNaPj.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaPj.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbqNaPj.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaPj.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbqNaPj.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaPj.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbqNaPj.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaPj.regs_out0 E' R' 17 Hregs) by (clear; lia). cbn [nth PbqNaPj.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaQ := BndP_Eb_038S9.LibSegEb_bqNaQ.
Definition KS_bqNaQ : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaQ.regs0 PbqNaQ.regs_out0).
Lemma KS_bqNaQ_ok : BG.kept_ok 80 PbqNaQ.regs0 PbqNaQ.regs_out0 KS_bqNaQ = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaQ_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 39%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 144) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 ((V 10%nat) + 24) -> getr R (reg 11) = Z_to_bv 64 ((V 39%nat) - 24) -> getr R (reg 12) = Z_to_bv 64 (V 50%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 10%nat) + 24) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 10%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880) ->
  140735332487296 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 32 -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  L5.writable RSEGS M (V 10%nat) 56 -> L5.writable RSEGS M ((V 2%nat) - 144) 16 -> (((V 2%nat) - 144) + 16 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 144)) -> L5.u64_at RSEGS M ((V 2%nat) - 136) 703824 ->
  4120 <= (V 39%nat) <= 140737488355328 -> aligned (V 39%nat) 8 -> 1 <= (V 50%nat) <= 4166 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 10%nat) + 32) <= bv_unsigned a < ((V 10%nat) + 32) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 10%nat) + 32) <= i < ((V 10%nat) + 32) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb35e8 M) (st fx' R' 0xb0aa8 M')
        /\ (forall x, In x KS_bqNaQ -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 703824
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 128)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 50%nat)
        /\ L5.u64_at RSEGS M' ((V 10%nat) + 32) ((V 39%nat) - 24)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 pvzI7 K1 pvzI8 K3 K4 K5 K6 K7 pvzI9 K9 pvzI10.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV39l; move HV39l before pvzI4; pose proof (proj2 pvzI4) as HV39r; move HV39r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV50l; move HV50l before pvzI6; pose proof (proj2 pvzI6) as HV50r; move HV50r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as K0l; move K0l before pvzI7; pose proof (proj2 pvzI7) as K0r; move K0r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as K2l; move K2l before pvzI8; pose proof (proj2 pvzI8) as K2r; move K2r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as K8l; move K8l before pvzI9; pose proof (proj2 pvzI9) as K8r; move K8r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K10l; move K10l before pvzI10; pose proof (proj2 pvzI10) as K10r; move K10r before pvzI10; clear pvzI10.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_39 := V 39%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 39%nat => Z_to_bv 64 vz_39 | 47%nat => Z_to_bv 64 vz_47 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 39%nat => vz_39 | 47%nat => vz_47 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbqNaQ.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaQ.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaQ.kn0).
  { unfold know_ok, PbqNaQ.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K2l K2r) | exact (conj K2l K2r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K2l K2r) | clear; lia | exact K3]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K2l K2r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K2l K2r; lia | clear - HV10l HV10r K2l K2r; lia | clear - HV10l HV10r K2l K2r; lia | exactA K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K2l K2r) | evalEk ZA ltac:(clear) | generalize K6; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K7]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV39l HV39r K8l K8r) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV39l HV39r K8l K8r) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K10l K10r) | exact (conj K10l K10r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaQ.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaQ.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_10 + 32) <= bv_unsigned a < (vz_10 + 32) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbqNaQ.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV10l HV10r K2l K2r) | evalEk' ZA Hag ltac:(clear) | clear - HV10l HV10r K2l K2r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaQ.ps0) with 0xb0aa8 in Hms. change (SR.ps_regs PbqNaQ.ps0) with (map (fun i => (i, nth i PbqNaQ.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaQ.ps0) with PbqNaQ.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaQ.regs0 PbqNaQ.regs_out0 80 KS_bqNaQ KS_bqNaQ_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaQ.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaQ.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbqNaQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaQ.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaQ.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV10l HV10r K2l K2r) | evalEk' ZA Hag ltac:(clear - HV39l HV39r K8l K8r) | clear; lia].
Qed.

Module PbqNaR0 := BndP_Eb_039S9.LibSegEb_bqNaR0.
Definition KS_bqNaR0 : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaR0.regs0 PbqNaR0.regs_out0).
Lemma KS_bqNaR0_ok : BG.kept_ok 80 PbqNaR0.regs0 PbqNaR0.regs_out0 KS_bqNaR0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaR0_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 10%nat) + 24) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 10%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) ->
  L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 48) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 76%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 38%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabd50 M) (st fx' R' 0xabe74 M')
        /\ (forall x, In x KS_bqNaR0 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 76%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450895) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450894) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450893) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450892) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.defined M' ((V 47%nat) + 8) 120).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 pvzI22 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI23 K4 K5 pvzI24 K7 K8 K9 K10 K11 K12 pvzI25 K14 K15 K16 K17 K18 K19 K20 K21 pvzI26 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI27 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV55l; move HV55l before pvzI7; pose proof (proj2 pvzI7) as HV55r; move HV55r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV56l; move HV56l before pvzI8; pose proof (proj2 pvzI8) as HV56r; move HV56r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV57l; move HV57l before pvzI9; pose proof (proj2 pvzI9) as HV57r; move HV57r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV64l; move HV64l before pvzI10; pose proof (proj2 pvzI10) as HV64r; move HV64r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV65l; move HV65l before pvzI11; pose proof (proj2 pvzI11) as HV65r; move HV65r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV66l; move HV66l before pvzI12; pose proof (proj2 pvzI12) as HV66r; move HV66r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV67l; move HV67l before pvzI13; pose proof (proj2 pvzI13) as HV67r; move HV67r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV68l; move HV68l before pvzI14; pose proof (proj2 pvzI14) as HV68r; move HV68r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV69l; move HV69l before pvzI15; pose proof (proj2 pvzI15) as HV69r; move HV69r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV70l; move HV70l before pvzI16; pose proof (proj2 pvzI16) as HV70r; move HV70r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV71l; move HV71l before pvzI17; pose proof (proj2 pvzI17) as HV71r; move HV71r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV72l; move HV72l before pvzI18; pose proof (proj2 pvzI18) as HV72r; move HV72r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV73l; move HV73l before pvzI19; pose proof (proj2 pvzI19) as HV73r; move HV73r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV74l; move HV74l before pvzI20; pose proof (proj2 pvzI20) as HV74r; move HV74r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV75l; move HV75l before pvzI21; pose proof (proj2 pvzI21) as HV75r; move HV75r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as HV76l; move HV76l before pvzI22; pose proof (proj2 pvzI22) as HV76r; move HV76r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K3l; move K3l before pvzI23; pose proof (proj2 pvzI23) as K3r; move K3r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K6l; move K6l before pvzI24; pose proof (proj2 pvzI24) as K6r; move K6r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K13l; move K13l before pvzI25; pose proof (proj2 pvzI25) as K13r; move K13r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K22l; move K22l before pvzI26; pose proof (proj2 pvzI26) as K22r; move K22r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K33l; move K33l before pvzI27; pose proof (proj2 pvzI27) as K33r; move K33r before pvzI27; clear pvzI27.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *. set (vz_76 := V 76%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | 76%nat => Z_to_bv 64 vz_76 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | 76%nat => vz_76 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 77%nat. }
  assert (HR: regs_ok E PbqNaR0.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaR0.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaR0.kn0).
  { unfold know_ok, PbqNaR0.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r; lia | clear - HV48l HV48r K13l K13r; lia | clear - HV48l HV48r K13l K13r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV76l HV76r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K47]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaR0.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaR0.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbqNaR0.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaR0.ps0) with 0xabe74 in Hms. change (SR.ps_regs PbqNaR0.ps0) with (map (fun i => (i, nth i PbqNaR0.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaR0.ps0) with PbqNaR0.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaR0.regs0 PbqNaR0.regs_out0 80 KS_bqNaR0 KS_bqNaR0_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR0.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbqNaR0.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaR1 := BndP_Eb_039S9.LibSegEb_bqNaR1.
Definition KS_bqNaR1 : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaR1.regs0 PbqNaR1.regs_out0).
Lemma KS_bqNaR1_ok : BG.kept_ok 80 PbqNaR1.regs0 PbqNaR1.regs_out0 KS_bqNaR1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaR1_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 42%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 10%nat) + 24) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 10%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) ->
  L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 48) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 76%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 51%nat) ->
  4120 <= (V 51%nat) <= 140737488355328 -> aligned (V 51%nat) 8 -> 24 <= ((V 51%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 51%nat) - 8) 8 ->
  (2147446784 + 17592186048512 <= ((V 51%nat) - 8) \/ ((V 51%nat) - 8) + 8 <= 2147446784) -> L5KA.zeros_at M ((((V 51%nat) - 8) / 8) + 2147450880) 1 -> (((V 51%nat) - 8) + 8 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 51%nat) - 8)) -> (((V 51%nat) - 8) + 8 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 51%nat) - 8)) ->
  (((V 51%nat) - 8) + 8 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 51%nat) - 8)) -> (((V 51%nat) - 8) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 51%nat) - 8)) -> (((((V 51%nat) - 8) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 51%nat) - 8) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 51%nat) - 8) (V 42%nat) ->
  0 <= (V 42%nat) <= 18446744073709551614 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 51%nat) - 8) <= bv_unsigned a < ((V 51%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 51%nat) - 8) <= i < ((V 51%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabd50 M) (st fx' R' 0xabe74 M')
        /\ (forall x, In x KS_bqNaR1 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 ((V 42%nat) + 1)
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 76%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450895) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450894) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450893) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450892) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 8) ((V 42%nat) + 1)
        /\ L5.defined M' ((V 47%nat) + 8) 120).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 pvzI22 pvzI23 pvzI24 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI25 K4 K5 pvzI26 K7 K8 K9 K10 K11 K12 pvzI27 K14 K15 K16 K17 K18 K19 K20 K21 pvzI28 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI29 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 pvzI30 K49 pvzI31 K51 K52 K53 K54 K55 K56 K57 K58 K59 pvzI32.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV42l; move HV42l before pvzI5; pose proof (proj2 pvzI5) as HV42r; move HV42r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV47l; move HV47l before pvzI6; pose proof (proj2 pvzI6) as HV47r; move HV47r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV48l; move HV48l before pvzI7; pose proof (proj2 pvzI7) as HV48r; move HV48r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV51l; move HV51l before pvzI8; pose proof (proj2 pvzI8) as HV51r; move HV51r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV55l; move HV55l before pvzI9; pose proof (proj2 pvzI9) as HV55r; move HV55r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV56l; move HV56l before pvzI10; pose proof (proj2 pvzI10) as HV56r; move HV56r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV57l; move HV57l before pvzI11; pose proof (proj2 pvzI11) as HV57r; move HV57r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV64l; move HV64l before pvzI12; pose proof (proj2 pvzI12) as HV64r; move HV64r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV65l; move HV65l before pvzI13; pose proof (proj2 pvzI13) as HV65r; move HV65r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV66l; move HV66l before pvzI14; pose proof (proj2 pvzI14) as HV66r; move HV66r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV67l; move HV67l before pvzI15; pose proof (proj2 pvzI15) as HV67r; move HV67r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV68l; move HV68l before pvzI16; pose proof (proj2 pvzI16) as HV68r; move HV68r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV69l; move HV69l before pvzI17; pose proof (proj2 pvzI17) as HV69r; move HV69r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV70l; move HV70l before pvzI18; pose proof (proj2 pvzI18) as HV70r; move HV70r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV71l; move HV71l before pvzI19; pose proof (proj2 pvzI19) as HV71r; move HV71r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV72l; move HV72l before pvzI20; pose proof (proj2 pvzI20) as HV72r; move HV72r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV73l; move HV73l before pvzI21; pose proof (proj2 pvzI21) as HV73r; move HV73r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as HV74l; move HV74l before pvzI22; pose proof (proj2 pvzI22) as HV74r; move HV74r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as HV75l; move HV75l before pvzI23; pose proof (proj2 pvzI23) as HV75r; move HV75r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as HV76l; move HV76l before pvzI24; pose proof (proj2 pvzI24) as HV76r; move HV76r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K3l; move K3l before pvzI25; pose proof (proj2 pvzI25) as K3r; move K3r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K6l; move K6l before pvzI26; pose proof (proj2 pvzI26) as K6r; move K6r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K13l; move K13l before pvzI27; pose proof (proj2 pvzI27) as K13r; move K13r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K22l; move K22l before pvzI28; pose proof (proj2 pvzI28) as K22r; move K22r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K33l; move K33l before pvzI29; pose proof (proj2 pvzI29) as K33r; move K33r before pvzI29; clear pvzI29. pose proof (proj1 pvzI30) as K48l; move K48l before pvzI30; pose proof (proj2 pvzI30) as K48r; move K48r before pvzI30; clear pvzI30. pose proof (proj1 pvzI31) as K50l; move K50l before pvzI31; pose proof (proj2 pvzI31) as K50r; move K50r before pvzI31; clear pvzI31. pose proof (proj1 pvzI32) as K60l; move K60l before pvzI32; pose proof (proj2 pvzI32) as K60r; move K60r before pvzI32; clear pvzI32.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_42 := V 42%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *. set (vz_76 := V 76%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 38%nat => Z_to_bv 64 vz_38 | 42%nat => Z_to_bv 64 vz_42 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 51%nat => Z_to_bv 64 vz_51 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | 76%nat => Z_to_bv 64 vz_76 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 38%nat => vz_38 | 42%nat => vz_42 | 47%nat => vz_47 | 48%nat => vz_48 | 51%nat => vz_51 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | 76%nat => vz_76 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 77%nat. }
  assert (HR: regs_ok E PbqNaR1.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaR1.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaR1.kn0).
  { unfold know_ok, PbqNaR1.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r; lia | clear - HV48l HV48r K13l K13r; lia | clear - HV48l HV48r K13l K13r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K50l K50r) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K50l K50r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV76l HV76r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | exact (conj K48l K48r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | clear; lia | exact K49]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K50l K50r HV51l HV51r K48l K48r) | exact (conj K50l K50r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K48l K48r K50l K50r; lia | clear - HV51l HV51r K48l K48r K50l K50r; lia | clear - HV51l HV51r K48l K48r K50l K50r; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K48l K48r K50l K50r; lia | clear - HV51l HV51r K48l K48r K50l K50r; lia | clear - HV51l HV51r K48l K48r K50l K50r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | generalize K54; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | generalize K55; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K56; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K57; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K58; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear - HV42l HV42r K60l K60r) | clear - HV51l HV51r K48l K48r K50l K50r; lia | clear - HV51l HV51r K48l K48r K50l K50r; lia | exactA K59]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV42l HV42r K60l K60r) | exact (conj K60l K60r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaR1.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaR1.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_51 - 8) <= bv_unsigned a < (vz_51 - 8) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbqNaR1.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K48l K48r K50l K50r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaR1.ps0) with 0xabe74 in Hms. change (SR.ps_regs PbqNaR1.ps0) with (map (fun i => (i, nth i PbqNaR1.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaR1.ps0) with PbqNaR1.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaR1.regs0 PbqNaR1.regs_out0 80 KS_bqNaR1 KS_bqNaR1_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbqNaR1.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk' ZA Hag ltac:(clear - HV42l HV42r K60l K60r) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaR1w := BndP_Eb_039S9.LibSegEb_bqNaR1w.
Definition KS_bqNaR1w : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaR1w.regs0 PbqNaR1w.regs_out0).
Lemma KS_bqNaR1w_ok : BG.kept_ok 80 PbqNaR1w.regs0 PbqNaR1w.regs_out0 KS_bqNaR1w = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaR1w_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 51%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 10%nat) + 24) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 10%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  (2147446784 + 17592186048512 <= (V 10%nat) \/ (V 10%nat) + 56 <= 2147446784) -> L5KA.zeros_at M (((V 10%nat) / 8) + 2147450880) 7 -> L5.writable RSEGS M (V 10%nat) 56 -> (((V 2%nat) - 128) + 128 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 2%nat) - 128)) ->
  L5KA.zeros_at M ((((V 10%nat) + 8) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 24) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 32) / 8) + 2147450880) 1 -> L5KA.zeros_at M ((((V 10%nat) + 48) / 8) + 2147450880) 1 ->
  L5.u64_at RSEGS M ((V 10%nat) + 24) (V 38%nat) -> 4096 <= (V 38%nat) <= 140737488355328 -> L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 104) (V 76%nat) -> L5.u64_at RSEGS M ((V 10%nat) + 32) (V 51%nat) ->
  4120 <= (V 51%nat) <= 140737488355328 -> aligned (V 51%nat) 8 -> 24 <= ((V 51%nat) - (V 38%nat)) <= 100000 -> L5.writable RSEGS M ((V 51%nat) - 8) 8 ->
  (2147446784 + 17592186048512 <= ((V 51%nat) - 8) \/ ((V 51%nat) - 8) + 8 <= 2147446784) -> L5KA.zeros_at M ((((V 51%nat) - 8) / 8) + 2147450880) 1 -> (((V 51%nat) - 8) + 8 <= ((V 2%nat) - 128) \/ ((V 2%nat) - 128) + 128 <= ((V 51%nat) - 8)) -> (((V 51%nat) - 8) + 8 <= (V 10%nat) \/ (V 10%nat) + 56 <= ((V 51%nat) - 8)) ->
  (((V 51%nat) - 8) + 8 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 51%nat) - 8)) -> (((V 51%nat) - 8) + 8 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 51%nat) - 8)) -> (((((V 51%nat) - 8) / 8) + 2147450880) + 1 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= ((((V 51%nat) - 8) / 8) + 2147450880)) -> L5.u64_at RSEGS M ((V 51%nat) - 8) 18446744073709551615 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 51%nat) - 8) <= bv_unsigned a < ((V 51%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 51%nat) - 8) <= i < ((V 51%nat) - 8) + 8) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabd50 M) (st fx' R' 0xabe74 M')
        /\ (forall x, In x KS_bqNaR1w -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 76%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450895) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450894) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450893) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450892) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.u64_at RSEGS M' ((V 51%nat) - 8) 0
        /\ L5.defined M' ((V 47%nat) + 8) 120).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 pvzI22 pvzI23 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI24 K4 K5 pvzI25 K7 K8 K9 K10 K11 K12 pvzI26 K14 K15 K16 K17 K18 K19 K20 K21 pvzI27 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 pvzI28 K34 K35 K36 K37 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 pvzI29 K49 pvzI30 K51 K52 K53 K54 K55 K56 K57 K58 K59.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV47l; move HV47l before pvzI5; pose proof (proj2 pvzI5) as HV47r; move HV47r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV48l; move HV48l before pvzI6; pose proof (proj2 pvzI6) as HV48r; move HV48r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV51l; move HV51l before pvzI7; pose proof (proj2 pvzI7) as HV51r; move HV51r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV55l; move HV55l before pvzI8; pose proof (proj2 pvzI8) as HV55r; move HV55r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV56l; move HV56l before pvzI9; pose proof (proj2 pvzI9) as HV56r; move HV56r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV57l; move HV57l before pvzI10; pose proof (proj2 pvzI10) as HV57r; move HV57r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV64l; move HV64l before pvzI11; pose proof (proj2 pvzI11) as HV64r; move HV64r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV65l; move HV65l before pvzI12; pose proof (proj2 pvzI12) as HV65r; move HV65r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV66l; move HV66l before pvzI13; pose proof (proj2 pvzI13) as HV66r; move HV66r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV67l; move HV67l before pvzI14; pose proof (proj2 pvzI14) as HV67r; move HV67r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV68l; move HV68l before pvzI15; pose proof (proj2 pvzI15) as HV68r; move HV68r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV69l; move HV69l before pvzI16; pose proof (proj2 pvzI16) as HV69r; move HV69r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV70l; move HV70l before pvzI17; pose proof (proj2 pvzI17) as HV70r; move HV70r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV71l; move HV71l before pvzI18; pose proof (proj2 pvzI18) as HV71r; move HV71r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV72l; move HV72l before pvzI19; pose proof (proj2 pvzI19) as HV72r; move HV72r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV73l; move HV73l before pvzI20; pose proof (proj2 pvzI20) as HV73r; move HV73r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV74l; move HV74l before pvzI21; pose proof (proj2 pvzI21) as HV74r; move HV74r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as HV75l; move HV75l before pvzI22; pose proof (proj2 pvzI22) as HV75r; move HV75r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as HV76l; move HV76l before pvzI23; pose proof (proj2 pvzI23) as HV76r; move HV76r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K3l; move K3l before pvzI24; pose proof (proj2 pvzI24) as K3r; move K3r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K6l; move K6l before pvzI25; pose proof (proj2 pvzI25) as K6r; move K6r before pvzI25; clear pvzI25. pose proof (proj1 pvzI26) as K13l; move K13l before pvzI26; pose proof (proj2 pvzI26) as K13r; move K13r before pvzI26; clear pvzI26. pose proof (proj1 pvzI27) as K22l; move K22l before pvzI27; pose proof (proj2 pvzI27) as K22r; move K22r before pvzI27; clear pvzI27. pose proof (proj1 pvzI28) as K33l; move K33l before pvzI28; pose proof (proj2 pvzI28) as K33r; move K33r before pvzI28; clear pvzI28. pose proof (proj1 pvzI29) as K48l; move K48l before pvzI29; pose proof (proj2 pvzI29) as K48r; move K48r before pvzI29; clear pvzI29. pose proof (proj1 pvzI30) as K50l; move K50l before pvzI30; pose proof (proj2 pvzI30) as K50r; move K50r before pvzI30; clear pvzI30.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_51 := V 51%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *. set (vz_76 := V 76%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 51%nat => Z_to_bv 64 vz_51 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | 76%nat => Z_to_bv 64 vz_76 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 51%nat => vz_51 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | 76%nat => vz_76 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 77%nat. }
  assert (HR: regs_ok E PbqNaR1w.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaR1w.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaR1w.kn0).
  { unfold know_ok, PbqNaR1w.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r; lia | clear - HV48l HV48r K13l K13r; lia | clear - HV48l HV48r K13l K13r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | generalize K24; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | generalize K27; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K28]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K50l K50r) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K50l K50r) | exact (conj K33l K33r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K36]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K37]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K38]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K39]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K42]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K43]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV76l HV76r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | clear - HV10l HV10r K22l K22r; lia | clear - HV10l HV10r K22l K22r; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | exact (conj K48l K48r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | clear; lia | exact K49]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K33l K33r K50l K50r HV51l HV51r K48l K48r) | exact (conj K50l K50r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K48l K48r K50l K50r; lia | clear - HV51l HV51r K48l K48r K50l K50r; lia | clear - HV51l HV51r K48l K48r K50l K50r; lia | exactA K51]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | generalize K52; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K48l K48r K50l K50r; lia | clear - HV51l HV51r K48l K48r K50l K50r; lia | clear - HV51l HV51r K48l K48r K50l K50r; lia | exactA K53]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | generalize K54; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | generalize K55; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K56; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K57; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K58; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk ZA ltac:(clear) | clear - HV51l HV51r K48l K48r K50l K50r; lia | clear - HV51l HV51r K48l K48r K50l K50r; lia | exactA K59]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaR1w.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaR1w.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_51 - 8) <= bv_unsigned a < (vz_51 - 8) + 8) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3. apply Hfr. unfold PbqNaR1w.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk' ZA Hag ltac:(clear) | clear - HV51l HV51r K48l K48r K50l K50r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r Hn3; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaR1w.ps0) with 0xabe74 in Hms. change (SR.ps_regs PbqNaR1w.ps0) with (map (fun i => (i, nth i PbqNaR1w.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaR1w.ps0) with PbqNaR1w.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaR1w.regs0 PbqNaR1w.regs_out0 80 KS_bqNaR1w KS_bqNaR1w_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaR1w.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbqNaR1w.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV51l HV51r K48l K48r K50l K50r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 19%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbqNaX := BndP_Eb_039S9.LibSegEb_bqNaX.
Definition KS_bqNaX : list nat := Eval vm_compute in (BG.kept_list 80 PbqNaX.regs0 PbqNaX.regs_out0).
Lemma KS_bqNaX_ok : BG.kept_ok 80 PbqNaX.regs0 PbqNaX.regs_out0 KS_bqNaX = true. Proof. vm_compute. reflexivity. Qed.
Lemma bqNaX_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 10%nat) < 2 ^ 64 -> 0 <= (V 12%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 55%nat) < 2 ^ 64 -> 0 <= (V 56%nat) < 2 ^ 64 -> 0 <= (V 57%nat) < 2 ^ 64 -> 0 <= (V 64%nat) < 2 ^ 64 -> 0 <= (V 65%nat) < 2 ^ 64 -> 0 <= (V 66%nat) < 2 ^ 64 -> 0 <= (V 67%nat) < 2 ^ 64 -> 0 <= (V 68%nat) < 2 ^ 64 -> 0 <= (V 69%nat) < 2 ^ 64 -> 0 <= (V 70%nat) < 2 ^ 64 -> 0 <= (V 71%nat) < 2 ^ 64 -> 0 <= (V 72%nat) < 2 ^ 64 -> 0 <= (V 73%nat) < 2 ^ 64 -> 0 <= (V 74%nat) < 2 ^ 64 -> 0 <= (V 75%nat) < 2 ^ 64 -> 0 <= (V 76%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 ((V 2%nat) - 128) -> getr R (reg 10) = Z_to_bv 64 (V 55%nat) -> getr R (reg 11) = Z_to_bv 64 (V 56%nat) -> getr R (reg 12) = Z_to_bv 64 (V 57%nat) -> getr R (reg 18) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 12%nat) -> getr R (reg 20) = Z_to_bv 64 ((V 10%nat) + 24) -> getr R (reg 21) = Z_to_bv 64 (V 10%nat) -> getr R (reg 22) = Z_to_bv 64 ((V 10%nat) + 32) -> getr R (reg 23) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 24) = Z_to_bv 64 (V 47%nat) -> getr R (reg 25) = Z_to_bv 64 2147450880 -> getr R (reg 26) = Z_to_bv 64 ((((V 10%nat) + 24) / 8) + 2147450880) -> getr R (reg 27) = Z_to_bv 64 ((((V 10%nat) + 32) / 8) + 2147450880) ->
  L5.img_clear M 1273856 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487296 <= (V 2%nat) <= 140737488355328 ->
  aligned (V 2%nat) 32 -> L5.writable RSEGS M ((V 2%nat) - 128) 128 -> 4096 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> (((V 2%nat) - 128) + 128 <= (V 47%nat) \/ (V 47%nat) + 128 <= ((V 2%nat) - 128)) -> (((V 2%nat) - 128) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= ((V 2%nat) - 128)) -> ((V 10%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 10%nat)) ->
  ((V 10%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 10%nat)) -> ((((V 10%nat) / 8) + 2147450880) + 7 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 10%nat) / 8) + 2147450880)) -> 4096 <= (V 10%nat) <= 140737488355272 -> aligned (V 10%nat) 8 ->
  L5.u64_at RSEGS M ((V 2%nat) - 8) (V 64%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 16) (V 65%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 24) (V 66%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 32) (V 67%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 40) (V 68%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 48) (V 69%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 56) (V 70%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 64) (V 71%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 72) (V 72%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 80) (V 73%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 88) (V 74%nat) -> L5.u64_at RSEGS M ((V 2%nat) - 96) (V 75%nat) ->
  L5.u64_at RSEGS M ((V 2%nat) - 104) (V 76%nat) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= bv_unsigned a < ((V 48%nat) + 0) + 1) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 48%nat) + 0) <= i < ((V 48%nat) + 0) + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xabd28 M) (st fx' R' 0xabe74 M')
        /\ (forall x, In x KS_bqNaX -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 (V 64%nat)
        /\ getr R' (reg 2) = Z_to_bv 64 (V 2%nat)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 65%nat)
        /\ getr R' (reg 9) = Z_to_bv 64 (V 66%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 1
        /\ getr R' (reg 18) = Z_to_bv 64 (V 67%nat)
        /\ getr R' (reg 19) = Z_to_bv 64 (V 68%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 69%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 (V 70%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 71%nat)
        /\ getr R' (reg 23) = Z_to_bv 64 (V 72%nat)
        /\ getr R' (reg 24) = Z_to_bv 64 (V 73%nat)
        /\ getr R' (reg 25) = Z_to_bv 64 (V 74%nat)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 75%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 (V 76%nat)
        /\ L5.u8_at RSEGS M' (V 48%nat) 0
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450895) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450894) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450893) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450892) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 245
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 245
        /\ L5.u64_at RSEGS M' (V 47%nat) 1172321806
        /\ L5.defined M' ((V 47%nat) + 8) 120).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 pvzI11 pvzI12 pvzI13 pvzI14 pvzI15 pvzI16 pvzI17 pvzI18 pvzI19 pvzI20 pvzI21 G2 G8 G9 G10 G11 G12 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 K0 K1 K2 pvzI22 K4 K5 pvzI23 K7 K8 K9 K10 K11 K12 pvzI24 K14 K15 K16 K17 K18 K19 K20 K21 pvzI25 K23 K24 K25 K26 K27 K28 K29 K30 K31 K32 K33 K34 K35 K36.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV10l; move HV10l before pvzI2; pose proof (proj2 pvzI2) as HV10r; move HV10r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV12l; move HV12l before pvzI3; pose proof (proj2 pvzI3) as HV12r; move HV12r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV47l; move HV47l before pvzI4; pose proof (proj2 pvzI4) as HV47r; move HV47r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV48l; move HV48l before pvzI5; pose proof (proj2 pvzI5) as HV48r; move HV48r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV55l; move HV55l before pvzI6; pose proof (proj2 pvzI6) as HV55r; move HV55r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV56l; move HV56l before pvzI7; pose proof (proj2 pvzI7) as HV56r; move HV56r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV57l; move HV57l before pvzI8; pose proof (proj2 pvzI8) as HV57r; move HV57r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV64l; move HV64l before pvzI9; pose proof (proj2 pvzI9) as HV64r; move HV64r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV65l; move HV65l before pvzI10; pose proof (proj2 pvzI10) as HV65r; move HV65r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as HV66l; move HV66l before pvzI11; pose proof (proj2 pvzI11) as HV66r; move HV66r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as HV67l; move HV67l before pvzI12; pose proof (proj2 pvzI12) as HV67r; move HV67r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as HV68l; move HV68l before pvzI13; pose proof (proj2 pvzI13) as HV68r; move HV68r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as HV69l; move HV69l before pvzI14; pose proof (proj2 pvzI14) as HV69r; move HV69r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as HV70l; move HV70l before pvzI15; pose proof (proj2 pvzI15) as HV70r; move HV70r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as HV71l; move HV71l before pvzI16; pose proof (proj2 pvzI16) as HV71r; move HV71r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as HV72l; move HV72l before pvzI17; pose proof (proj2 pvzI17) as HV72r; move HV72r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as HV73l; move HV73l before pvzI18; pose proof (proj2 pvzI18) as HV73r; move HV73r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as HV74l; move HV74l before pvzI19; pose proof (proj2 pvzI19) as HV74r; move HV74r before pvzI19; clear pvzI19. pose proof (proj1 pvzI20) as HV75l; move HV75l before pvzI20; pose proof (proj2 pvzI20) as HV75r; move HV75r before pvzI20; clear pvzI20. pose proof (proj1 pvzI21) as HV76l; move HV76l before pvzI21; pose proof (proj2 pvzI21) as HV76r; move HV76r before pvzI21; clear pvzI21. pose proof (proj1 pvzI22) as K3l; move K3l before pvzI22; pose proof (proj2 pvzI22) as K3r; move K3r before pvzI22; clear pvzI22. pose proof (proj1 pvzI23) as K6l; move K6l before pvzI23; pose proof (proj2 pvzI23) as K6r; move K6r before pvzI23; clear pvzI23. pose proof (proj1 pvzI24) as K13l; move K13l before pvzI24; pose proof (proj2 pvzI24) as K13r; move K13r before pvzI24; clear pvzI24. pose proof (proj1 pvzI25) as K22l; move K22l before pvzI25; pose proof (proj2 pvzI25) as K22r; move K22r before pvzI25; clear pvzI25.
  set (vz_2 := V 2%nat) in *. set (vz_10 := V 10%nat) in *. set (vz_12 := V 12%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_55 := V 55%nat) in *. set (vz_56 := V 56%nat) in *. set (vz_57 := V 57%nat) in *. set (vz_64 := V 64%nat) in *. set (vz_65 := V 65%nat) in *. set (vz_66 := V 66%nat) in *. set (vz_67 := V 67%nat) in *. set (vz_68 := V 68%nat) in *. set (vz_69 := V 69%nat) in *. set (vz_70 := V 70%nat) in *. set (vz_71 := V 71%nat) in *. set (vz_72 := V 72%nat) in *. set (vz_73 := V 73%nat) in *. set (vz_74 := V 74%nat) in *. set (vz_75 := V 75%nat) in *. set (vz_76 := V 76%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 10%nat => Z_to_bv 64 vz_10 | 12%nat => Z_to_bv 64 vz_12 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 55%nat => Z_to_bv 64 vz_55 | 56%nat => Z_to_bv 64 vz_56 | 57%nat => Z_to_bv 64 vz_57 | 64%nat => Z_to_bv 64 vz_64 | 65%nat => Z_to_bv 64 vz_65 | 66%nat => Z_to_bv 64 vz_66 | 67%nat => Z_to_bv 64 vz_67 | 68%nat => Z_to_bv 64 vz_68 | 69%nat => Z_to_bv 64 vz_69 | 70%nat => Z_to_bv 64 vz_70 | 71%nat => Z_to_bv 64 vz_71 | 72%nat => Z_to_bv 64 vz_72 | 73%nat => Z_to_bv 64 vz_73 | 74%nat => Z_to_bv 64 vz_74 | 75%nat => Z_to_bv 64 vz_75 | 76%nat => Z_to_bv 64 vz_76 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 10%nat => vz_10 | 12%nat => vz_12 | 47%nat => vz_47 | 48%nat => vz_48 | 55%nat => vz_55 | 56%nat => vz_56 | 57%nat => vz_57 | 64%nat => vz_64 | 65%nat => vz_65 | 66%nat => vz_66 | 67%nat => vz_67 | 68%nat => vz_68 | 69%nat => vz_69 | 70%nat => vz_70 | 71%nat => vz_71 | 72%nat => vz_72 | 73%nat => vz_73 | 74%nat => vz_74 | 75%nat => vz_75 | 76%nat => vz_76 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 77%nat. }
  assert (HR: regs_ok E PbqNaX.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbqNaX.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbqNaX.kn0).
  { unfold know_ok, PbqNaX.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | exact (conj K6l K6r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | clear; lia | exact K7]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | clear - HV47l HV47r K6l K6r; lia | clear - HV47l HV47r K6l K6r; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | exact (conj K13l K13r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K13l K13r; lia | clear - HV48l HV48r K13l K13r; lia | clear - HV48l HV48r K13l K13r; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K15; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K17; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K18; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K19; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K13l K13r) | evalEk ZA ltac:(clear) | generalize K20; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K6l K6r) | evalEk ZA ltac:(clear) | generalize K21; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV10l HV10r K22l K22r) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV64l HV64r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV65l HV65r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV66l HV66r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV67l HV67r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV68l HV68r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV69l HV69r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K29]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV70l HV70r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV71l HV71r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K31]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV72l HV72r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K32]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV73l HV73r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K33]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV74l HV74r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K34]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV75l HV75r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K35]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV2l HV2r K3l K3r) | evalEk ZA ltac:(clear - HV76l HV76r) | clear - HV2l HV2r K3l K3r; lia | clear - HV2l HV2r K3l K3r; lia | exactA K36]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbqNaX.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbqNaX.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_48 + 0) <= bv_unsigned a < (vz_48 + 0) + 1) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2. apply Hfr. unfold PbqNaX.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K6l K6r Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r) | evalEk' ZA Hag ltac:(clear) | clear - HV48l HV48r K13l K13r Hn2; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbqNaX.ps0) with 0xabe74 in Hms. change (SR.ps_regs PbqNaX.ps0) with (map (fun i => (i, nth i PbqNaX.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbqNaX.ps0) with PbqNaX.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbqNaX.regs0 PbqNaX.regs_out0 80 KS_bqNaX KS_bqNaX_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbqNaX.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbqNaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaX.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbqNaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaX.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbqNaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaX.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbqNaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaX.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbqNaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaX.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbqNaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaX.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbqNaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaX.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbqNaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaX.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbqNaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaX.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbqNaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaX.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbqNaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaX.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbqNaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaX.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbqNaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaX.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbqNaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbqNaX.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbqNaX.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 0%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV48l HV48r K13l K13r) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 1%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 2%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 3%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 16%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 18%nat); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K6l K6r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

End PEBENDP1.
