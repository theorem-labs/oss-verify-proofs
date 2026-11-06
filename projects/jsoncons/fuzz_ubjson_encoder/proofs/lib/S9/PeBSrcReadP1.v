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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.seg Require BndP_Eb_053S9 BndP_Eb_054S9.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMBSRP1.
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

Module PbsrA := BndP_Eb_053S9.LibSegEb_bsrA.
Definition KS_bsrA : list nat := Eval vm_compute in (BG.kept_list 80 PbsrA.regs0 PbsrA.regs_out0).
Lemma KS_bsrA_ok : BG.kept_ok 80 PbsrA.regs0 PbsrA.regs_out0 KS_bsrA = true. Proof. vm_compute. reflexivity. Qed.
Lemma bsrA_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 (V 38%nat) ->
  140735332487328 <= (V 2%nat) <= 140737488355328 -> aligned (V 2%nat) 16 -> L5.writable RSEGS M ((V 2%nat) - 160) 160 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 2%nat) - 160) <= bv_unsigned a < ((V 2%nat) - 160) + 160) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 2%nat) - 160) <= i < ((V 2%nat) - 160) + 160) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9148 M) (st fx' R' 0xb9188 M')
        /\ (forall x, In x KS_bsrA -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 2) = Z_to_bv 64 ((V 2%nat) - 160)
        /\ getr R' (reg 8) = Z_to_bv 64 (V 2%nat)
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
        /\ L5.u64_at RSEGS M' ((V 2%nat) - 160) 0).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 G2 G10 G11 G12 pvzI5 K1 K2.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as K0l; move K0l before pvzI5; pose proof (proj2 pvzI5) as K0r; move K0r before pvzI5; clear pvzI5.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 39%nat. }
  assert (HR: regs_ok E PbsrA.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbsrA.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbsrA.kn0).
  { unfold know_ok, PbsrA.kn0.
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | exact (conj K0l K0r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | clear; lia | exact K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV2l HV2r K0l K0r) | evalEk ZA ltac:(clear) | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | clear - HV2l HV2r K0l K0r; lia | exactA K2]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbsrA.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbsrA.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_2 - 160) <= bv_unsigned a < (vz_2 - 160) + 160) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbsrA.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear - HV2l HV2r K0l K0r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbsrA.ps0) with 0xb9188 in Hms. change (SR.ps_regs PbsrA.ps0) with (map (fun i => (i, nth i PbsrA.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbsrA.ps0) with PbsrA.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbsrA.regs0 PbsrA.regs_out0 80 KS_bsrA KS_bsrA_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbsrA.regs_out0 E' R' 2 Hregs) by (clear; lia). cbn [nth PbsrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrA.regs_out0 E' R' 8 Hregs) by (clear; lia). cbn [nth PbsrA.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV2l HV2r K0l K0r) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbsrA2 := BndP_Eb_053S9.LibSegEb_bsrA2.
Definition KS_bsrA2 : list nat := Eval vm_compute in (BG.kept_list 80 PbsrA2.regs0 PbsrA2.regs_out0).
Lemma KS_bsrA2_ok : BG.kept_ok 80 PbsrA2.regs0 PbsrA2.regs_out0 KS_bsrA2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bsrA2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 50%nat) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 10) = Z_to_bv 64 (V 36%nat) -> getr R (reg 11) = Z_to_bv 64 (V 37%nat) -> getr R (reg 12) = Z_to_bv 64 (V 38%nat) ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487168 <= (V 50%nat) <= 140737488355168 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 56 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 24) <= bv_unsigned a < ((V 50%nat) + 24) + 8) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 24) <= i < ((V 50%nat) + 24) + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb918c M) (st fx' R' 0x5edb0 M')
        /\ (forall x, In x KS_bsrA2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 758208
        /\ getr R' (reg 9) = Z_to_bv 64 (V 50%nat)
        /\ getr R' (reg 10) = Z_to_bv 64 96
        /\ getr R' (reg 11) = Z_to_bv 64 1335544
        /\ getr R' (reg 12) = Z_to_bv 64 1
        /\ getr R' (reg 19) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 22) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 27) = Z_to_bv 64 2147450880
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 24) (V 37%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 G2 G8 G10 G11 G12 K0 K1 K2 pvzI6 K4 K5.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV36l; move HV36l before pvzI2; pose proof (proj2 pvzI2) as HV36r; move HV36r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV37l; move HV37l before pvzI3; pose proof (proj2 pvzI3) as HV37r; move HV37r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV38l; move HV38l before pvzI4; pose proof (proj2 pvzI4) as HV38r; move HV38r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV50l; move HV50l before pvzI5; pose proof (proj2 pvzI5) as HV50r; move HV50r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as K3l; move K3l before pvzI6; pose proof (proj2 pvzI6) as K3r; move K3r before pvzI6; clear pvzI6.
  set (vz_2 := V 2%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbsrA2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbsrA2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbsrA2.kn0).
  { unfold know_ok, PbsrA2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r; lia | clear - HV50l HV50r K3l K3r; lia | clear - HV50l HV50r K3l K3r; lia | exactA K5]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbsrA2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbsrA2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 24) <= bv_unsigned a < (vz_50 + 24) + 8) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbsrA2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbsrA2.ps0) with 0x5edb0 in Hms. change (SR.ps_regs PbsrA2.ps0) with (map (fun i => (i, nth i PbsrA2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbsrA2.ps0) with PbsrA2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbsrA2.regs0 PbsrA2.regs_out0 80 KS_bsrA2 KS_bsrA2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbsrA2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbsrA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrA2.regs_out0 E' R' 9 Hregs) by (clear; lia). cbn [nth PbsrA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrA2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbsrA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrA2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbsrA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrA2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbsrA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrA2.regs_out0 E' R' 19 Hregs) by (clear; lia). cbn [nth PbsrA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrA2.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbsrA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrA2.regs_out0 E' R' 27 Hregs) by (clear; lia). cbn [nth PbsrA2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r) | evalEk' ZA Hag ltac:(clear - HV37l HV37r) | clear; lia].
Qed.

Module PbsrB1ge := BndP_Eb_054S9.LibSegEb_bsrB1ge.
Definition KS_bsrB1ge : list nat := Eval vm_compute in (BG.kept_list 80 PbsrB1ge.regs0 PbsrB1ge.regs_out0).
Lemma KS_bsrB1ge_ok : BG.kept_ok 80 PbsrB1ge.regs0 PbsrB1ge.regs_out0 KS_bsrB1ge = true. Proof. vm_compute. reflexivity. Qed.
Lemma bsrB1ge_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 50%nat) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 (V 50%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487168 <= (V 50%nat) <= 140737488355168 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 56 -> L5.u64_at RSEGS M ((V 50%nat) + 24) (V 37%nat) -> 4096 <= (V 37%nat) <= 140737488338944 ->
  6930432 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 ->
  L5.writable RSEGS M (V 36%nat) 296 -> ((V 50%nat) + 56 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 50%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.defined M ((V 36%nat) + 256) 8 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) -> 6930432 <= (V 47%nat) <= 140737488355200 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 -> L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> ((V 36%nat) + 296 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 36%nat)) ->
  ((V 36%nat) + 296 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 37 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 50%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 50%nat)) -> ((V 50%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 50%nat)) ->
  ((V 47%nat) + 128 <= 65536 \/ 65536 + 1200196 <= (V 47%nat)) -> 1 <= (V 33%nat) <= 16384 -> 1 <= (V 38%nat) <= 16384 -> 0 <= (((-1) * (V 33%nat)) + (V 38%nat)) <= 16383 ->
  4096 <= (V 35%nat) <= 140737488338944 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 56) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 56) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb91c0 M) (st fx' R' 0x78e40 M')
        /\ (forall x, In x KS_bsrB1ge -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 758480
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551602
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 16) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 36%nat) + 280)
        /\ getr R' (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) ((V 47%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 48) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) (V 38%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 758088
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 127645
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 24) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.defined M' ((V 36%nat) + 256) 8
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) (V 33%nat)
        /\ L5.defined M' ((V 47%nat) + 24) 8
        /\ L5.defined M' ((V 47%nat) + 40) 88
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G19 G22 G27 K0 K1 K2 pvzI11 K4 K5 K6 pvzI12 pvzI13 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 pvzI14 K20 K21 K22 K23 K24 K25 K26 pvzI15 K28 K29 K30 K31 K32 K33 K34 K35 K36 pvzI16 pvzI17 pvzI18 pvzI19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV47l; move HV47l before pvzI8; pose proof (proj2 pvzI8) as HV47r; move HV47r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV50l; move HV50l before pvzI10; pose proof (proj2 pvzI10) as HV50r; move HV50r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K19l; move K19l before pvzI14; pose proof (proj2 pvzI14) as K19r; move K19r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K27l; move K27l before pvzI15; pose proof (proj2 pvzI15) as K27r; move K27r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K37l; move K37l before pvzI16; pose proof (proj2 pvzI16) as K37r; move K37r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K38l; move K38l before pvzI17; pose proof (proj2 pvzI17) as K38r; move K38r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K39l; move K39l before pvzI18; pose proof (proj2 pvzI18) as K39r; move K39r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K40l; move K40l before pvzI19; pose proof (proj2 pvzI19) as K40r; move K40r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbsrB1ge.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbsrB1ge.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbsrB1ge.kn0).
  { unfold know_ok, PbsrB1ge.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K13 K34 K35; lia | clear - HV50l HV50r K3l K3r K13 K34 K35; lia | clear - HV50l HV50r K3l K3r K13 K34 K35; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | clear - HV50l HV50r K3l K3r K13 K34 K35; lia | clear - HV50l HV50r K3l K3r K13 K34 K35; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear - HV35l HV35r K40l K40r) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear - HV33l HV33r K37l K37r K39l K39r) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | exactA K24]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K27l K27r K29 K30 K32 K35; lia | clear - HV48l HV48r K27l K27r K29 K30 K32 K35; lia | clear - HV48l HV48r K27l K27r K29 K30 K32 K35; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K37l K37r K39l K39r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K38l K38r K39l K39r) | exact (conj K38l K38r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K37l K37r K39l K39r HV38l HV38r K38l K38r) | exact (conj K39l K39r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K40l K40r) | exact (conj K40l K40r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbsrB1ge.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbsrB1ge.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 56) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4. apply Hfr. unfold PbsrB1ge.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K13 K34 K35 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 Hn4; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbsrB1ge.ps0) with 0x78e40 in Hms. change (SR.ps_regs PbsrB1ge.ps0) with (map (fun i => (i, nth i PbsrB1ge.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbsrB1ge.ps0) with PbsrB1ge.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbsrB1ge.regs0 PbsrB1ge.regs_out0 80 KS_bsrB1ge KS_bsrB1ge_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbsrB1ge.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbsrB1ge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1ge.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbsrB1ge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1ge.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbsrB1ge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1ge.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbsrB1ge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1ge.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbsrB1ge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1ge.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbsrB1ge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1ge.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbsrB1ge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1ge.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbsrB1ge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1ge.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbsrB1ge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1ge.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbsrB1ge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1ge.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbsrB1ge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1ge.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbsrB1ge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1ge.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbsrB1ge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1ge.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbsrB1ge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1ge.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbsrB1ge.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K38l K38r K39l K39r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K7l K7r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 22); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K40l K40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K37l K37r K39l K39r) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 25); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 26); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 27); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbsrB1lt := BndP_Eb_054S9.LibSegEb_bsrB1lt.
Definition KS_bsrB1lt : list nat := Eval vm_compute in (BG.kept_list 80 PbsrB1lt.regs0 PbsrB1lt.regs_out0).
Lemma KS_bsrB1lt_ok : BG.kept_ok 80 PbsrB1lt.regs0 PbsrB1lt.regs_out0 KS_bsrB1lt = true. Proof. vm_compute. reflexivity. Qed.
Lemma bsrB1lt_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 50%nat) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 (V 50%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487168 <= (V 50%nat) <= 140737488355168 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 56 -> L5.u64_at RSEGS M ((V 50%nat) + 24) (V 37%nat) -> 4096 <= (V 37%nat) <= 140737488338944 ->
  6930432 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 ->
  L5.writable RSEGS M (V 36%nat) 296 -> ((V 50%nat) + 56 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 50%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.defined M ((V 36%nat) + 256) 8 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) -> 6930432 <= (V 47%nat) <= 140737488355200 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 -> L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> ((V 36%nat) + 296 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 36%nat)) ->
  ((V 36%nat) + 296 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 37 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 50%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 50%nat)) -> ((V 50%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 50%nat)) ->
  ((V 47%nat) + 128 <= 65536 \/ 65536 + 1200196 <= (V 47%nat)) -> 2 <= (V 33%nat) <= 16384 -> 1 <= (V 38%nat) <= 16383 -> 1 <= ((V 33%nat) - (V 38%nat)) <= 16383 ->
  4096 <= (V 35%nat) <= 140737488338944 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 56) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 56) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb91c0 M) (st fx' R' 0xb9298 M')
        /\ (forall x, In x KS_bsrB1lt -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 33%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 ((V 47%nat) + 32)
        /\ getr R' (reg 13) = Z_to_bv 64 18446744073709551602
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 16) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) ((V 47%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 48) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) (V 38%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 758088
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 127645
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 24) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.defined M' ((V 36%nat) + 256) 8
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) (V 33%nat)
        /\ L5.defined M' ((V 47%nat) + 24) 8
        /\ L5.defined M' ((V 47%nat) + 40) 88
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G19 G22 G27 K0 K1 K2 pvzI11 K4 K5 K6 pvzI12 pvzI13 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 pvzI14 K20 K21 K22 K23 K24 K25 K26 pvzI15 K28 K29 K30 K31 K32 K33 K34 K35 K36 pvzI16 pvzI17 pvzI18 pvzI19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV47l; move HV47l before pvzI8; pose proof (proj2 pvzI8) as HV47r; move HV47r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV50l; move HV50l before pvzI10; pose proof (proj2 pvzI10) as HV50r; move HV50r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K8l; move K8l before pvzI13; pose proof (proj2 pvzI13) as K8r; move K8r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K19l; move K19l before pvzI14; pose proof (proj2 pvzI14) as K19r; move K19r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K27l; move K27l before pvzI15; pose proof (proj2 pvzI15) as K27r; move K27r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K37l; move K37l before pvzI16; pose proof (proj2 pvzI16) as K37r; move K37r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K38l; move K38l before pvzI17; pose proof (proj2 pvzI17) as K38r; move K38r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K39l; move K39l before pvzI18; pose proof (proj2 pvzI18) as K39r; move K39r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K40l; move K40l before pvzI19; pose proof (proj2 pvzI19) as K40r; move K40r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbsrB1lt.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbsrB1lt.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbsrB1lt.kn0).
  { unfold know_ok, PbsrB1lt.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K13 K34 K35; lia | clear - HV50l HV50r K3l K3r K13 K34 K35; lia | clear - HV50l HV50r K3l K3r K13 K34 K35; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | clear - HV50l HV50r K3l K3r K13 K34 K35; lia | clear - HV50l HV50r K3l K3r K13 K34 K35; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear - HV35l HV35r K40l K40r) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear - HV33l HV33r K37l K37r K39l K39r) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | exactA K24]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K27l K27r K29 K30 K32 K35; lia | clear - HV48l HV48r K27l K27r K29 K30 K32 K35; lia | clear - HV48l HV48r K27l K27r K29 K30 K32 K35; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K37l K37r K39l K39r) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K38l K38r K39l K39r) | exact (conj K38l K38r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K37l K37r K39l K39r HV38l HV38r K38l K38r) | exact (conj K39l K39r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K40l K40r) | exact (conj K40l K40r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbsrB1lt.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbsrB1lt.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 56) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4. apply Hfr. unfold PbsrB1lt.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K13 K34 K35 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 Hn4; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbsrB1lt.ps0) with 0xb9298 in Hms. change (SR.ps_regs PbsrB1lt.ps0) with (map (fun i => (i, nth i PbsrB1lt.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbsrB1lt.ps0) with PbsrB1lt.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbsrB1lt.regs0 PbsrB1lt.regs_out0 80 KS_bsrB1lt KS_bsrB1lt_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbsrB1lt.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbsrB1lt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbsrB1lt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbsrB1lt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbsrB1lt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbsrB1lt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbsrB1lt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbsrB1lt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbsrB1lt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbsrB1lt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbsrB1lt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbsrB1lt.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K38l K38r K39l K39r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K7l K7r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 22); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K40l K40r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K37l K37r K39l K39r) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 25); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 26); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 27); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbsrB1lt2 := BndP_Eb_054S9.LibSegEb_bsrB1lt2.
Definition KS_bsrB1lt2 : list nat := Eval vm_compute in (BG.kept_list 80 PbsrB1lt2.regs0 PbsrB1lt2.regs_out0).
Lemma KS_bsrB1lt2_ok : BG.kept_ok 80 PbsrB1lt2.regs0 PbsrB1lt2.regs_out0 KS_bsrB1lt2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma bsrB1lt2_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 33%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 50%nat) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 (V 50%nat) -> getr R (reg 10) = Z_to_bv 64 ((V 47%nat) + 32) -> getr R (reg 11) = Z_to_bv 64 (V 33%nat) -> getr R (reg 18) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) -> getr R (reg 23) = Z_to_bv 64 ((V 36%nat) + 288) -> getr R (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880) -> getr R (reg 26) = Z_to_bv 64 (V 47%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487168 <= (V 50%nat) <= 140737488355168 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 56 -> L5.u64_at RSEGS M ((V 50%nat) + 24) (V 37%nat) -> 4096 <= (V 37%nat) <= 140737488338944 ->
  L5.u64_at RSEGS M ((V 50%nat) + 8) ((V 47%nat) + 32) -> L5.u64_at RSEGS M ((V 50%nat) + 16) (V 47%nat) -> L5.u64_at RSEGS M ((V 50%nat) + 48) (V 47%nat) -> 6930432 <= (V 36%nat) <= 140737488355032 ->
  aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 -> L5.writable RSEGS M (V 36%nat) 296 ->
  ((V 50%nat) + 56 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 50%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 -> L5.defined M ((V 36%nat) + 256) 8 ->
  L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) (V 33%nat) -> 6930432 <= (V 47%nat) <= 140737488355200 -> aligned (V 47%nat) 32 ->
  L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) -> L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 ->
  L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 -> L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) ->
  ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> ((V 36%nat) + 296 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 36%nat)) -> ((V 36%nat) + 296 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 37 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 36%nat) / 8) + 2147450880)) ->
  ((V 50%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 50%nat)) -> ((V 50%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 50%nat)) -> ((V 47%nat) + 128 <= 65536 \/ 65536 + 1200196 <= (V 47%nat)) -> L5.u64_at RSEGS M ((V 47%nat) + 32) (V 38%nat) ->
  L5KA.zeros_at M ((((V 47%nat) + 32) / 8) + 2147450880) 1 -> 2 <= (V 33%nat) <= 16384 -> 1 <= (V 38%nat) <= 16383 -> 1 <= ((V 33%nat) - (V 38%nat)) <= 16383 ->
  4096 <= (V 35%nat) <= 140737488338944 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb9298 M) (st fx' R' 0x78e40 M')
        /\ (forall x, In x KS_bsrB1lt2 -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 758480
        /\ getr R' (reg 10) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 35%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 20) = Z_to_bv 64 (V 38%nat)
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880)
        /\ getr R' (reg 24) = Z_to_bv 64 ((V 36%nat) + 280)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.defined M' ((V 36%nat) + 256) 8
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) (V 33%nat)).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 pvzI10 G2 G8 G9 G10 G11 G18 G19 G22 G23 G25 G26 G27 K0 K1 K2 pvzI11 K4 K5 K6 pvzI12 K8 K9 K10 pvzI13 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 pvzI14 K23 K24 K25 K26 K27 K28 pvzI15 K30 K31 K32 K33 K34 K35 K36 K37 K38 K39 K40 pvzI16 pvzI17 pvzI18 pvzI19.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV33l; move HV33l before pvzI2; pose proof (proj2 pvzI2) as HV33r; move HV33r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV34l; move HV34l before pvzI3; pose proof (proj2 pvzI3) as HV34r; move HV34r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV35l; move HV35l before pvzI4; pose proof (proj2 pvzI4) as HV35r; move HV35r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV36l; move HV36l before pvzI5; pose proof (proj2 pvzI5) as HV36r; move HV36r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV37l; move HV37l before pvzI6; pose proof (proj2 pvzI6) as HV37r; move HV37r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV38l; move HV38l before pvzI7; pose proof (proj2 pvzI7) as HV38r; move HV38r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV47l; move HV47l before pvzI8; pose proof (proj2 pvzI8) as HV47r; move HV47r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV48l; move HV48l before pvzI9; pose proof (proj2 pvzI9) as HV48r; move HV48r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as HV50l; move HV50l before pvzI10; pose proof (proj2 pvzI10) as HV50r; move HV50r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K3l; move K3l before pvzI11; pose proof (proj2 pvzI11) as K3r; move K3r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K7l; move K7l before pvzI12; pose proof (proj2 pvzI12) as K7r; move K7r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K11l; move K11l before pvzI13; pose proof (proj2 pvzI13) as K11r; move K11r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K22l; move K22l before pvzI14; pose proof (proj2 pvzI14) as K22r; move K22r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K29l; move K29l before pvzI15; pose proof (proj2 pvzI15) as K29r; move K29r before pvzI15; clear pvzI15. pose proof (proj1 pvzI16) as K41l; move K41l before pvzI16; pose proof (proj2 pvzI16) as K41r; move K41r before pvzI16; clear pvzI16. pose proof (proj1 pvzI17) as K42l; move K42l before pvzI17; pose proof (proj2 pvzI17) as K42r; move K42r before pvzI17; clear pvzI17. pose proof (proj1 pvzI18) as K43l; move K43l before pvzI18; pose proof (proj2 pvzI18) as K43r; move K43r before pvzI18; clear pvzI18. pose proof (proj1 pvzI19) as K44l; move K44l before pvzI19; pose proof (proj2 pvzI19) as K44r; move K44r before pvzI19; clear pvzI19.
  set (vz_2 := V 2%nat) in *. set (vz_33 := V 33%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 33%nat => Z_to_bv 64 vz_33 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 33%nat => vz_33 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbsrB1lt2.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbsrB1lt2.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbsrB1lt2.kn0).
  { unfold know_ok, PbsrB1lt2.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K16 K36 K37; lia | clear - HV50l HV50r K3l K3r K16 K36 K37; lia | clear - HV50l HV50r K3l K3r K16 K36 K37; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37) | evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | clear - HV50l HV50r K3l K3r K16 K36 K37; lia | clear - HV50l HV50r K3l K3r K16 K36 K37; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | clear - HV50l HV50r K3l K3r K16 K36 K37; lia | clear - HV50l HV50r K3l K3r K16 K36 K37; lia | exactA K8]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | clear - HV50l HV50r K3l K3r K16 K36 K37; lia | clear - HV50l HV50r K3l K3r K16 K36 K37; lia | exactA K9]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | clear - HV50l HV50r K3l K3r K16 K36 K37; lia | clear - HV50l HV50r K3l K3r K16 K36 K37; lia | exactA K10]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | exact (conj K11l K11r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | clear; lia | exact K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk ZA ltac:(clear) | generalize K16; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | exactA K19]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk ZA ltac:(clear - HV35l HV35r K44l K44r) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | exactA K20]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk ZA ltac:(clear - HV33l HV33r K41l K41r K43l K43r) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | exact (conj K22l K22r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | clear; lia | exact K23]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | exactA K24]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | generalize K26; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | exactA K27]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37) | exact (conj K29l K29r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K29l K29r K31 K32 K34 K37; lia | clear - HV48l HV48r K29l K29r K31 K32 K34 K37; lia | clear - HV48l HV48r K29l K29r K31 K32 K34 K37; lia | exactA K30]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K16 K36 K37) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K29l K29r K31 K32 K34 K37) | evalEk ZA ltac:(clear) | generalize K37; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K38; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | evalEk ZA ltac:(clear - HV38l HV38r K42l K42r K43l K43r) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | exactA K39]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | clear - HV47l HV47r K22l K22r K26 K32 K33 K35 K36 K38; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K41l K41r K43l K43r) | exact (conj K41l K41r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K42l K42r K43l K43r) | exact (conj K42l K42r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV33l HV33r K41l K41r K43l K43r HV38l HV38r K42l K42r) | exact (conj K43l K43r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV35l HV35r K44l K44r) | exact (conj K44l K44r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbsrB1lt2.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbsrB1lt2.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0. apply Hfr. unfold PbsrB1lt2.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35 Hn0; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbsrB1lt2.ps0) with 0x78e40 in Hms. change (SR.ps_regs PbsrB1lt2.ps0) with (map (fun i => (i, nth i PbsrB1lt2.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbsrB1lt2.ps0) with PbsrB1lt2.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbsrB1lt2.regs0 PbsrB1lt2.regs_out0 80 KS_bsrB1lt2 KS_bsrB1lt2_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbsrB1lt2.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbsrB1lt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt2.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbsrB1lt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt2.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbsrB1lt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt2.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbsrB1lt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt2.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbsrB1lt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt2.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbsrB1lt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB1lt2.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbsrB1lt2.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk' ZA Hag ltac:(clear - HV35l HV35r K44l K44r) | clear; lia]. }
  eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K11l K11r K13 K16 K33 K34 K35) | evalEk' ZA Hag ltac:(clear - HV33l HV33r K41l K41r K43l K43r) | clear; lia].
Qed.

Module PbsrB0f := BndP_Eb_054S9.LibSegEb_bsrB0f.
Definition KS_bsrB0f : list nat := Eval vm_compute in (BG.kept_list 80 PbsrB0f.regs0 PbsrB0f.regs_out0).
Lemma KS_bsrB0f_ok : BG.kept_ok 80 PbsrB0f.regs0 PbsrB0f.regs_out0 KS_bsrB0f = true. Proof. vm_compute. reflexivity. Qed.
Lemma bsrB0f_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 38%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 50%nat) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 (V 50%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 (V 38%nat) -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487168 <= (V 50%nat) <= 140737488355168 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 56 -> L5.u64_at RSEGS M ((V 50%nat) + 24) (V 37%nat) -> 4096 <= (V 37%nat) <= 140737488338944 ->
  6930432 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 ->
  L5.writable RSEGS M (V 36%nat) 296 -> ((V 50%nat) + 56 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 50%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.defined M ((V 36%nat) + 256) 8 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> 6930432 <= (V 47%nat) <= 140737488355200 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 -> L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> ((V 36%nat) + 296 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 36%nat)) ->
  ((V 36%nat) + 296 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 37 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 50%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 50%nat)) -> ((V 50%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 50%nat)) ->
  ((V 47%nat) + 128 <= 65536 \/ 65536 + 1200196 <= (V 47%nat)) -> 1 <= (V 38%nat) <= 16383 ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 56) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 56) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb91c0 M) (st fx' R' 0xb9944 M')
        /\ (forall x, In x KS_bsrB0f -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 758680
        /\ getr R' (reg 10) = Z_to_bv 64 (V 36%nat)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 34%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 16384
        /\ getr R' (reg 13) = Z_to_bv 64 16384
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 16) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 0
        /\ getr R' (reg 21) = Z_to_bv 64 ((((V 36%nat) + 280) / 8) + 2147450880)
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 36%nat) + 280)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) ((V 47%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 48) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) (V 38%nat)
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 758088
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 127645
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 24) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.defined M' ((V 36%nat) + 256) 8
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.defined M' ((V 47%nat) + 24) 8
        /\ L5.defined M' ((V 47%nat) + 40) 88
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G19 G22 G27 K0 K1 K2 pvzI10 K4 K5 K6 pvzI11 pvzI12 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 pvzI13 K20 K21 K22 K23 K24 K25 K26 pvzI14 K28 K29 K30 K31 K32 K33 K34 K35 K36 pvzI15.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV38l; move HV38l before pvzI6; pose proof (proj2 pvzI6) as HV38r; move HV38r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV47l; move HV47l before pvzI7; pose proof (proj2 pvzI7) as HV47r; move HV47r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K7l; move K7l before pvzI11; pose proof (proj2 pvzI11) as K7r; move K7r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K8l; move K8l before pvzI12; pose proof (proj2 pvzI12) as K8r; move K8r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K19l; move K19l before pvzI13; pose proof (proj2 pvzI13) as K19r; move K19r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K27l; move K27l before pvzI14; pose proof (proj2 pvzI14) as K27r; move K27r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K37l; move K37l before pvzI15; pose proof (proj2 pvzI15) as K37r; move K37r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_38 := V 38%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 38%nat => Z_to_bv 64 vz_38 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 38%nat => vz_38 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbsrB0f.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbsrB0f.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbsrB0f.kn0).
  { unfold know_ok, PbsrB0f.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K13 K34 K35; lia | clear - HV50l HV50r K3l K3r K13 K34 K35; lia | clear - HV50l HV50r K3l K3r K13 K34 K35; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | clear - HV50l HV50r K3l K3r K13 K34 K35; lia | clear - HV50l HV50r K3l K3r K13 K34 K35; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | exactA K24]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K27l K27r K29 K30 K32 K35; lia | clear - HV48l HV48r K27l K27r K29 K30 K32 K35; lia | clear - HV48l HV48r K27l K27r K29 K30 K32 K35; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV38l HV38r K37l K37r) | exact (conj K37l K37r)]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbsrB0f.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbsrB0f.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 56) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4. apply Hfr. unfold PbsrB0f.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K13 K34 K35 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 Hn4; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbsrB0f.ps0) with 0xb9944 in Hms. change (SR.ps_regs PbsrB0f.ps0) with (map (fun i => (i, nth i PbsrB0f.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbsrB0f.ps0) with PbsrB0f.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbsrB0f.regs0 PbsrB0f.regs_out0 80 KS_bsrB0f KS_bsrB0f_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbsrB0f.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbsrB0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0f.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbsrB0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0f.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbsrB0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0f.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbsrB0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0f.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbsrB0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0f.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbsrB0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0f.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbsrB0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0f.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbsrB0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0f.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbsrB0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0f.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbsrB0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0f.regs_out0 E' R' 21 Hregs) by (clear; lia). cbn [nth PbsrB0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0f.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbsrB0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0f.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbsrB0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0f.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbsrB0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0f.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbsrB0f.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear - HV38l HV38r K37l K37r) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 16); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K7l K7r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 23); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 25); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 26); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 27); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbsrB0x := BndP_Eb_054S9.LibSegEb_bsrB0x.
Definition KS_bsrB0x : list nat := Eval vm_compute in (BG.kept_list 80 PbsrB0x.regs0 PbsrB0x.regs_out0).
Lemma KS_bsrB0x_ok : BG.kept_ok 80 PbsrB0x.regs0 PbsrB0x.regs_out0 KS_bsrB0x = true. Proof. vm_compute. reflexivity. Qed.
Lemma bsrB0x_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 50%nat) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 (V 50%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 16384 -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487168 <= (V 50%nat) <= 140737488355168 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 56 -> L5.u64_at RSEGS M ((V 50%nat) + 24) (V 37%nat) -> 4096 <= (V 37%nat) <= 140737488338944 ->
  6930432 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 ->
  L5.writable RSEGS M (V 36%nat) 296 -> ((V 50%nat) + 56 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 50%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.defined M ((V 36%nat) + 256) 8 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> 6930432 <= (V 47%nat) <= 140737488355200 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 -> L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> ((V 36%nat) + 296 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 36%nat)) ->
  ((V 36%nat) + 296 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 37 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 50%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 50%nat)) -> ((V 50%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 50%nat)) ->
  ((V 47%nat) + 128 <= 65536 \/ 65536 + 1200196 <= (V 47%nat)) -> 6930432 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 -> (2147446784 + 17592186048512 <= (V 45%nat) \/ (V 45%nat) + 272 <= 2147446784) ->
  L5KA.zeros_at M (((V 45%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 45%nat) 272 -> ((V 36%nat) + 296 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) -> ((V 50%nat) + 56 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 50%nat)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 240) (V 45%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 45%nat) + 16) -> L5.u64_at RSEGS M (V 45%nat) 1291576 -> L5.u64_at RSEGS M ((V 45%nat) + 16) 1291336 ->
  L5.u32_at RSEGS M ((V 45%nat) + 152) 0 -> L5.u32_at RSEGS M ((V 45%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 160) ((V 45%nat) + 16) -> L5KA.zeros_at M 2147612324 1 ->
  L5KA.zeros_at M 2147612305 1 -> ((V 45%nat) + 272 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 45%nat)) -> ((V 45%nat) + 272 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 45%nat)) -> ((((V 47%nat) / 8) + 2147450880) + 16 <= (((V 45%nat) / 8) + 2147450880) \/ (((V 45%nat) / 8) + 2147450880) + 34 <= (((V 47%nat) / 8) + 2147450880)) ->
  ((((V 47%nat) / 8) + 2147450880) + 16 <= 2147612324 \/ 2147612324 + 1 <= (((V 47%nat) / 8) + 2147450880)) -> ((((V 47%nat) / 8) + 2147450880) + 16 <= 2147612305 \/ 2147612305 + 1 <= (((V 47%nat) / 8) + 2147450880)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 56) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 56) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb91c0 M) (st fx' R' 0xe0b2c M')
        /\ (forall x, In x KS_bsrB0x -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 1) = Z_to_bv 64 759144
        /\ getr R' (reg 10) = Z_to_bv 64 ((V 45%nat) + 16)
        /\ getr R' (reg 11) = Z_to_bv 64 (V 37%nat)
        /\ getr R' (reg 12) = Z_to_bv 64 16384
        /\ getr R' (reg 13) = Z_to_bv 64 920364
        /\ getr R' (reg 14) = Z_to_bv 64 0
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 16) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 ((V 36%nat) + 240)
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 24) = Z_to_bv 64 ((((V 36%nat) + 240) / 8) + 2147450880)
        /\ getr R' (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) ((V 47%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 48) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) 16384
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 758088
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 127645
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 24) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.defined M' ((V 36%nat) + 256) 8
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 35%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.defined M' ((V 47%nat) + 24) 8
        /\ L5.defined M' ((V 47%nat) + 40) 88
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G19 G22 G27 K0 K1 K2 pvzI10 K4 K5 K6 pvzI11 pvzI12 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 pvzI13 K20 K21 K22 K23 K24 K25 K26 pvzI14 K28 K29 K30 K31 K32 K33 K34 K35 K36 pvzI15 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV47l; move HV47l before pvzI7; pose proof (proj2 pvzI7) as HV47r; move HV47r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K7l; move K7l before pvzI11; pose proof (proj2 pvzI11) as K7r; move K7r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K8l; move K8l before pvzI12; pose proof (proj2 pvzI12) as K8r; move K8r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K19l; move K19l before pvzI13; pose proof (proj2 pvzI13) as K19r; move K19r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K27l; move K27l before pvzI14; pose proof (proj2 pvzI14) as K27r; move K27r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K37l; move K37l before pvzI15; pose proof (proj2 pvzI15) as K37r; move K37r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 45%nat => Z_to_bv 64 vz_45 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 45%nat => vz_45 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbsrB0x.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbsrB0x.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbsrB0x.kn0).
  { unfold know_ok, PbsrB0x.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K13 K34 K35 K43; lia | clear - HV50l HV50r K3l K3r K13 K34 K35 K43; lia | clear - HV50l HV50r K3l K3r K13 K34 K35 K43; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | clear - HV50l HV50r K3l K3r K13 K34 K35 K43; lia | clear - HV50l HV50r K3l K3r K13 K34 K35 K43; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | exactA K24]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54; lia | clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54; lia | clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | exactA K50]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K51]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | evalEk ZA ltac:(clear) | generalize K54; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | generalize K55; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K56; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K57; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbsrB0x.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbsrB0x.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 56) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4. apply Hfr. unfold PbsrB0x.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K13 K34 K35 K43 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42 Hn4; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbsrB0x.ps0) with 0xe0b2c in Hms. change (SR.ps_regs PbsrB0x.ps0) with (map (fun i => (i, nth i PbsrB0x.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbsrB0x.ps0) with PbsrB0x.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbsrB0x.regs0 PbsrB0x.regs_out0 80 KS_bsrB0x KS_bsrB0x_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbsrB0x.regs_out0 E' R' 1 Hregs) by (clear; lia). cbn [nth PbsrB0x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0x.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbsrB0x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0x.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbsrB0x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0x.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbsrB0x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0x.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbsrB0x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0x.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbsrB0x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0x.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbsrB0x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0x.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbsrB0x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0x.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbsrB0x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0x.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbsrB0x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0x.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbsrB0x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0x.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbsrB0x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0x.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbsrB0x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0x.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbsrB0x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0x.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbsrB0x.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 15); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 16); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K7l K7r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 22); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 23); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 25); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 26); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 27); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

Module PbsrB0e := BndP_Eb_053S9.LibSegEb_bsrB0e.
Definition KS_bsrB0e : list nat := Eval vm_compute in (BG.kept_list 80 PbsrB0e.regs0 PbsrB0e.regs_out0).
Lemma KS_bsrB0e_ok : BG.kept_ok 80 PbsrB0e.regs0 PbsrB0e.regs_out0 KS_bsrB0e = true. Proof. vm_compute. reflexivity. Qed.
Lemma bsrB0e_conc fx R M (V : nat -> Z) :
  0 <= (V 2%nat) < 2 ^ 64 -> 0 <= (V 34%nat) < 2 ^ 64 -> 0 <= (V 35%nat) < 2 ^ 64 -> 0 <= (V 36%nat) < 2 ^ 64 -> 0 <= (V 37%nat) < 2 ^ 64 -> 0 <= (V 45%nat) < 2 ^ 64 -> 0 <= (V 47%nat) < 2 ^ 64 -> 0 <= (V 48%nat) < 2 ^ 64 -> 0 <= (V 50%nat) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (V 50%nat) -> getr R (reg 8) = Z_to_bv 64 (V 2%nat) -> getr R (reg 9) = Z_to_bv 64 (V 50%nat) -> getr R (reg 10) = Z_to_bv 64 (V 47%nat) -> getr R (reg 19) = Z_to_bv 64 (V 36%nat) -> getr R (reg 22) = Z_to_bv 64 16384 -> getr R (reg 27) = Z_to_bv 64 2147450880 ->
  L5.img_clear M 65536 1306624 -> L5.u64_at RSEGS M 1335544 2147450880 -> L5.u32_at RSEGS M 1335552 1 -> 140735332487168 <= (V 50%nat) <= 140737488355168 ->
  aligned (V 50%nat) 32 -> L5.writable RSEGS M (V 50%nat) 56 -> L5.u64_at RSEGS M ((V 50%nat) + 24) (V 37%nat) -> 4096 <= (V 37%nat) <= 140737488338944 ->
  6930432 <= (V 36%nat) <= 140737488355032 -> aligned (V 36%nat) 8 -> (2147446784 + 17592186048512 <= (V 36%nat) \/ (V 36%nat) + 296 <= 2147446784) -> L5KA.zeros_at M ((((V 36%nat) + 8) / 8) + 2147450880) 36 ->
  L5.writable RSEGS M (V 36%nat) 296 -> ((V 50%nat) + 56 <= (V 36%nat) \/ (V 36%nat) + 296 <= (V 50%nat)) -> L5.u64_at RSEGS M ((V 36%nat) + 264) (V 34%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 272) 16384 ->
  L5.defined M ((V 36%nat) + 256) 8 -> L5.u64_at RSEGS M ((V 36%nat) + 280) (V 35%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 288) 0 -> 6930432 <= (V 47%nat) <= 140737488355200 ->
  aligned (V 47%nat) 32 -> L5.defined M (V 47%nat) 128 -> L5.writable RSEGS M (V 47%nat) 128 -> (2147446784 + 17592186048512 <= (V 47%nat) \/ (V 47%nat) + 128 <= 2147446784) ->
  L5.writable RSEGS M (((V 47%nat) / 8) + 2147450880) 16 -> L5KA.zeros_at M (((V 47%nat) / 8) + 2147450880) 16 -> L5.u64_at RSEGS M ((V 47%nat) + 120) (V 48%nat) -> 4096 <= (V 48%nat) <= 140737488355327 ->
  L5.writable RSEGS M (V 48%nat) 1 -> (2147446784 + 17592186048512 <= (V 48%nat) \/ (V 48%nat) + 1 <= 2147446784) -> ((V 47%nat) + 128 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 47%nat)) -> ((V 36%nat) + 296 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 36%nat)) ->
  ((V 36%nat) + 296 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 36%nat)) -> ((((V 36%nat) / 8) + 2147450880) + 37 <= (((V 47%nat) / 8) + 2147450880) \/ (((V 47%nat) / 8) + 2147450880) + 16 <= (((V 36%nat) / 8) + 2147450880)) -> ((V 50%nat) + 56 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 50%nat)) -> ((V 50%nat) + 56 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 50%nat)) ->
  ((V 47%nat) + 128 <= 65536 \/ 65536 + 1200196 <= (V 47%nat)) -> 6930432 <= (V 45%nat) <= 140737488355056 -> aligned (V 45%nat) 8 -> (2147446784 + 17592186048512 <= (V 45%nat) \/ (V 45%nat) + 272 <= 2147446784) ->
  L5KA.zeros_at M (((V 45%nat) / 8) + 2147450880) 34 -> L5.writable RSEGS M (V 45%nat) 272 -> ((V 36%nat) + 296 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 36%nat)) -> ((V 50%nat) + 56 <= (V 45%nat) \/ (V 45%nat) + 272 <= (V 50%nat)) ->
  L5.u64_at RSEGS M ((V 36%nat) + 240) (V 45%nat) -> L5.u64_at RSEGS M ((V 36%nat) + 248) ((V 45%nat) + 16) -> L5.u64_at RSEGS M (V 45%nat) 1291576 -> L5.u64_at RSEGS M ((V 45%nat) + 16) 1291336 ->
  L5.u32_at RSEGS M ((V 45%nat) + 152) 2 -> L5.u32_at RSEGS M ((V 45%nat) + 156) 0 -> L5.u64_at RSEGS M ((V 45%nat) + 160) ((V 45%nat) + 16) -> L5KA.zeros_at M 2147612324 1 ->
  L5KA.zeros_at M 2147612305 1 -> ((V 45%nat) + 272 <= (V 47%nat) \/ (V 47%nat) + 128 <= (V 45%nat)) -> ((V 45%nat) + 272 <= (V 48%nat) \/ (V 48%nat) + 1 <= (V 45%nat)) -> ((((V 47%nat) / 8) + 2147450880) + 16 <= (((V 45%nat) / 8) + 2147450880) \/ (((V 45%nat) / 8) + 2147450880) + 34 <= (((V 47%nat) / 8) + 2147450880)) ->
  ((((V 47%nat) / 8) + 2147450880) + 16 <= 2147612324 \/ 2147612324 + 1 <= (((V 47%nat) / 8) + 2147450880)) -> ((((V 47%nat) / 8) + 2147450880) + 16 <= 2147612305 \/ 2147612305 + 1 <= (((V 47%nat) / 8) + 2147450880)) ->
  exists fx' R' M', mem_grows M M'
    /\ (forall a : word, ~ (((V 50%nat) + 0) <= bv_unsigned a < ((V 50%nat) + 0) + 56) -> ~ (((V 47%nat) + 0) <= bv_unsigned a < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= bv_unsigned a < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= bv_unsigned a < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= bv_unsigned a < ((V 36%nat) + 256) + 40) -> M' a = M a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (((V 50%nat) + 0) <= i < ((V 50%nat) + 0) + 56) -> ~ (((V 47%nat) + 0) <= i < ((V 47%nat) + 0) + 24) -> ~ (((V 47%nat) + 32) <= i < ((V 47%nat) + 32) + 8) -> ~ (((((V 47%nat) / 8) + 2147450880) + 0) <= i < ((((V 47%nat) / 8) + 2147450880) + 0) + 16) -> ~ (((V 36%nat) + 256) <= i < ((V 36%nat) + 256) + 40) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb91c0 M) (st fx' R' 0xb9628 M')
        /\ (forall x, In x KS_bsrB0e -> getr R' (reg x) = getr R (reg x))
        /\ getr R' (reg 10) = Z_to_bv 64 0
        /\ getr R' (reg 11) = Z_to_bv 64 0
        /\ getr R' (reg 12) = Z_to_bv 64 16384
        /\ getr R' (reg 13) = Z_to_bv 64 0
        /\ getr R' (reg 14) = Z_to_bv 64 18446744073709551601
        /\ getr R' (reg 15) = Z_to_bv 64 18446744073709551603
        /\ getr R' (reg 16) = Z_to_bv 64 (V 47%nat)
        /\ getr R' (reg 18) = Z_to_bv 64 ((((V 36%nat) + 288) / 8) + 2147450880)
        /\ getr R' (reg 20) = Z_to_bv 64 0
        /\ getr R' (reg 22) = Z_to_bv 64 0
        /\ getr R' (reg 23) = Z_to_bv 64 ((V 36%nat) + 288)
        /\ getr R' (reg 24) = Z_to_bv 64 ((((V 36%nat) + 240) / 8) + 2147450880)
        /\ getr R' (reg 25) = Z_to_bv 64 (((V 47%nat) / 8) + 2147450880)
        /\ getr R' (reg 26) = Z_to_bv 64 (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 288) 0
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 8) ((V 47%nat) + 32)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 16) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 48) (V 47%nat)
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 32) 16384
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450891) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450890) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450889) 243
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450888) 248
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450883) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450882) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450881) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450880) 241
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450887) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450886) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450885) 242
        /\ L5.u8_at RSEGS M' (((V 47%nat) / 8) + 2147450884) 0
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 16) 758088
        /\ L5.u64_at RSEGS M' ((V 47%nat) + 8) 127645
        /\ L5.u64_at RSEGS M' (V 47%nat) 1102416563
        /\ L5.u64_at RSEGS M' ((V 50%nat) + 24) (V 37%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 264) (V 34%nat)
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 272) 16384
        /\ L5.defined M' ((V 36%nat) + 256) 8
        /\ L5.u64_at RSEGS M' ((V 36%nat) + 280) (V 35%nat)
        /\ L5.defined M' ((V 47%nat) + 24) 8
        /\ L5.defined M' ((V 47%nat) + 40) 88
        /\ L5KA.zeros_at M' (((V 47%nat) / 8) + 2147450892) 4).
Proof.
  intros pvzI1 pvzI2 pvzI3 pvzI4 pvzI5 pvzI6 pvzI7 pvzI8 pvzI9 G2 G8 G9 G10 G19 G22 G27 K0 K1 K2 pvzI10 K4 K5 K6 pvzI11 pvzI12 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 pvzI13 K20 K21 K22 K23 K24 K25 K26 pvzI14 K28 K29 K30 K31 K32 K33 K34 K35 K36 pvzI15 K38 K39 K40 K41 K42 K43 K44 K45 K46 K47 K48 K49 K50 K51 K52 K53 K54 K55 K56 K57.
  pose proof (proj1 pvzI1) as HV2l; move HV2l before pvzI1; pose proof (proj2 pvzI1) as HV2r; move HV2r before pvzI1; clear pvzI1. pose proof (proj1 pvzI2) as HV34l; move HV34l before pvzI2; pose proof (proj2 pvzI2) as HV34r; move HV34r before pvzI2; clear pvzI2. pose proof (proj1 pvzI3) as HV35l; move HV35l before pvzI3; pose proof (proj2 pvzI3) as HV35r; move HV35r before pvzI3; clear pvzI3. pose proof (proj1 pvzI4) as HV36l; move HV36l before pvzI4; pose proof (proj2 pvzI4) as HV36r; move HV36r before pvzI4; clear pvzI4. pose proof (proj1 pvzI5) as HV37l; move HV37l before pvzI5; pose proof (proj2 pvzI5) as HV37r; move HV37r before pvzI5; clear pvzI5. pose proof (proj1 pvzI6) as HV45l; move HV45l before pvzI6; pose proof (proj2 pvzI6) as HV45r; move HV45r before pvzI6; clear pvzI6. pose proof (proj1 pvzI7) as HV47l; move HV47l before pvzI7; pose proof (proj2 pvzI7) as HV47r; move HV47r before pvzI7; clear pvzI7. pose proof (proj1 pvzI8) as HV48l; move HV48l before pvzI8; pose proof (proj2 pvzI8) as HV48r; move HV48r before pvzI8; clear pvzI8. pose proof (proj1 pvzI9) as HV50l; move HV50l before pvzI9; pose proof (proj2 pvzI9) as HV50r; move HV50r before pvzI9; clear pvzI9. pose proof (proj1 pvzI10) as K3l; move K3l before pvzI10; pose proof (proj2 pvzI10) as K3r; move K3r before pvzI10; clear pvzI10. pose proof (proj1 pvzI11) as K7l; move K7l before pvzI11; pose proof (proj2 pvzI11) as K7r; move K7r before pvzI11; clear pvzI11. pose proof (proj1 pvzI12) as K8l; move K8l before pvzI12; pose proof (proj2 pvzI12) as K8r; move K8r before pvzI12; clear pvzI12. pose proof (proj1 pvzI13) as K19l; move K19l before pvzI13; pose proof (proj2 pvzI13) as K19r; move K19r before pvzI13; clear pvzI13. pose proof (proj1 pvzI14) as K27l; move K27l before pvzI14; pose proof (proj2 pvzI14) as K27r; move K27r before pvzI14; clear pvzI14. pose proof (proj1 pvzI15) as K37l; move K37l before pvzI15; pose proof (proj2 pvzI15) as K37r; move K37r before pvzI15; clear pvzI15.
  set (vz_2 := V 2%nat) in *. set (vz_34 := V 34%nat) in *. set (vz_35 := V 35%nat) in *. set (vz_36 := V 36%nat) in *. set (vz_37 := V 37%nat) in *. set (vz_45 := V 45%nat) in *. set (vz_47 := V 47%nat) in *. set (vz_48 := V 48%nat) in *. set (vz_50 := V 50%nat) in *.
  set (E := Env (fun j : nat => match j with 2%nat => Z_to_bv 64 vz_2 | 34%nat => Z_to_bv 64 vz_34 | 35%nat => Z_to_bv 64 vz_35 | 36%nat => Z_to_bv 64 vz_36 | 37%nat => Z_to_bv 64 vz_37 | 45%nat => Z_to_bv 64 vz_45 | 47%nat => Z_to_bv 64 vz_47 | 48%nat => Z_to_bv 64 vz_48 | 50%nat => Z_to_bv 64 vz_50 | _ => getr R (reg j) end) (fun _ => [])).
  set (VzN := (fun j : nat => match j with 2%nat => vz_2 | 34%nat => vz_34 | 35%nat => vz_35 | 36%nat => vz_36 | 37%nat => vz_37 | 45%nat => vz_45 | 47%nat => vz_47 | 48%nat => vz_48 | 50%nat => vz_50 | _ => bv_unsigned (getr R (reg j)) end)).
  assert (ZA : forall j, bv_unsigned (ev E j) = VzN j).
  { unfold VzN. BigLinkZA.za_tac0 51%nat. }
  assert (HR: regs_ok E PbsrB0e.regs0 R). { apply BG.regs_ok_of_slots. reflexivity. cbn [BG.slots tl PbsrB0e.regs0 nth]. apc_norm. repeat split; slotP ZA. }
  assert (HK: know_ok RSEGS E M PbsrB0e.kn0).
  { unfold know_ok, PbsrB0e.kn0.
    apply Forall_cons. { eapply L5K.kentry_KImg; [clear; lia | clear; lia | exact K0]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K1]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | exactA K2]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | exact (conj K3l K3r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | clear; lia | exact K4]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk ZA ltac:(clear) | clear - HV50l HV50r K3l K3r K13 K34 K35 K43; lia | clear - HV50l HV50r K3l K3r K13 K34 K35 K43; lia | clear - HV50l HV50r K3l K3r K13 K34 K35 K43; lia | exactA K5]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | clear - HV50l HV50r K3l K3r K13 K34 K35 K43; lia | clear - HV50l HV50r K3l K3r K13 K34 K35 K43; lia | exactA K6]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV37l HV37r K7l K7r) | exact (conj K7l K7r)]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | exact (conj K8l K8r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | clear; lia | exact K9]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | generalize K10; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K11]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K12]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | generalize K13; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear - HV34l HV34r) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K14]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K15]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K16]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear - HV35l HV35r) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K17]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K18]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | exact (conj K19l K19r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | clear; lia | exact K20]. }
    apply Forall_cons. { eapply L5K.kentry_KUnk; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | exactA K21]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | exactA K22]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | generalize K23; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | exactA K24]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | exactA K25]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57; lia | exactA K26]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | exact (conj K27l K27r)]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | evalEk ZA ltac:(clear) | clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54; lia | clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54; lia | clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54; lia | exactA K28]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | evalEk ZA ltac:(clear) | generalize K29; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | evalEk ZA ltac:(clear) | generalize K30; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | generalize K31; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | evalEk ZA ltac:(clear) | generalize K32; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | generalize K33; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | generalize K34; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | evalEk ZA ltac:(clear) | generalize K35; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K36; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KRange; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | exact (conj K37l K37r)]. }
    apply Forall_cons. { eapply L5K.kentry_KAlign; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | clear; lia | exact K38]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | generalize K39; clear; intro; lia]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | exactA K40]. }
    apply Forall_cons. { eapply L5K.kentry_KWr; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | exactA K41]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | generalize K42; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | generalize K43; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K44]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42; lia | exactA K45]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | exactA K46]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | exactA K47]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | exactA K48]. }
    apply Forall_cons. { eapply L5K.kentry_KWord4; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | exactA K49]. }
    apply Forall_cons. { eapply L5K.kentry_KWord8; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55; lia | exactA K50]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K51]. }
    apply Forall_cons. { eapply L5KA.kentry_KZero; [evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | clear; lia | clear; lia | clear; lia | exactA K52]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | generalize K53; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV48l HV48r K27l K27r K29 K30 K32 K35 K54) | evalEk ZA ltac:(clear) | generalize K54; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear - HV45l HV45r K37l K37r K39 K42 K43 K53 K54 K55) | evalEk ZA ltac:(clear) | generalize K55; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K56; clear; intro; lia]. }
    apply Forall_cons. { eapply L5K.kentry_KDisj; [evalEk ZA ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | evalEk ZA ltac:(clear) | generalize K57; clear; intro; lia]. }
    apply Forall_nil. }
  pvz_hg ltac:(idtac; destruct (PbsrB0e.seg_sound_ax fx E R M HR HK ltac:(constructor)) as (fx' & E' & R' & M' & kk & ps & Hnth & Hag & Hms & Hregs & Hx0 & Hrok & Hfr & Hcells & Hgr)).
  change PbsrB0e.NX0 with 80%nat in Hag.
  exists fx', R', M'. pvz_linconj. split. exact Hgr.
  assert (FRW: forall a : word, ~ ((vz_50 + 0) <= bv_unsigned a < (vz_50 + 0) + 56) -> ~ ((vz_47 + 0) <= bv_unsigned a < (vz_47 + 0) + 24) -> ~ ((vz_47 + 32) <= bv_unsigned a < (vz_47 + 32) + 8) -> ~ ((((vz_47 / 8) + 2147450880) + 0) <= bv_unsigned a < (((vz_47 / 8) + 2147450880) + 0) + 16) -> ~ ((vz_36 + 256) <= bv_unsigned a < (vz_36 + 256) + 40) -> M' a = M a).
  { intros a Hn0 Hn1 Hn2 Hn3 Hn4. apply Hfr. unfold PbsrB0e.F0.
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk' ZA Hag ltac:(clear) | clear - HV50l HV50r K3l K3r K13 K34 K35 K43 Hn0; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57 Hn1; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57 Hn2; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57 Hn3; lia |].
    eapply L5K.outside_cons_e; [evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk' ZA Hag ltac:(clear) | clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42 Hn4; lia |].
    apply L5K.outside_nil_e. }
  split. exact FRW.
  split. { intros i Hi Hn0 Hn1 Hn2 Hn3 Hn4. apply FRW; rewrite ?BG.unsigned_lit by exact Hi; assumption. }
  apply L5K.nth_error_single in Hnth. subst ps.
  change (SR.ps_pc PbsrB0e.ps0) with 0xb9628 in Hms. change (SR.ps_regs PbsrB0e.ps0) with (map (fun i => (i, nth i PbsrB0e.regs_out0 (ELit 0))) (seq 1 31)) in Hregs.
  change (SR.ps_cells PbsrB0e.ps0) with PbsrB0e.cells0 in Hcells.
  split. { exact Hms. }
  split. { intros j Hj. apply (BG.kept_regs E E' R R' PbsrB0e.regs0 PbsrB0e.regs_out0 80 KS_bsrB0e KS_bsrB0e_ok HR Hag Hregs j Hj). }
  split. { rewrite (BG.out_reg PbsrB0e.regs_out0 E' R' 10 Hregs) by (clear; lia). cbn [nth PbsrB0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0e.regs_out0 E' R' 11 Hregs) by (clear; lia). cbn [nth PbsrB0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0e.regs_out0 E' R' 12 Hregs) by (clear; lia). cbn [nth PbsrB0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0e.regs_out0 E' R' 13 Hregs) by (clear; lia). cbn [nth PbsrB0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0e.regs_out0 E' R' 14 Hregs) by (clear; lia). cbn [nth PbsrB0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0e.regs_out0 E' R' 15 Hregs) by (clear; lia). cbn [nth PbsrB0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0e.regs_out0 E' R' 16 Hregs) by (clear; lia). cbn [nth PbsrB0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0e.regs_out0 E' R' 18 Hregs) by (clear; lia). cbn [nth PbsrB0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0e.regs_out0 E' R' 20 Hregs) by (clear; lia). cbn [nth PbsrB0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0e.regs_out0 E' R' 22 Hregs) by (clear; lia). cbn [nth PbsrB0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0e.regs_out0 E' R' 23 Hregs) by (clear; lia). cbn [nth PbsrB0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0e.regs_out0 E' R' 24 Hregs) by (clear; lia). cbn [nth PbsrB0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0e.regs_out0 E' R' 25 Hregs) by (clear; lia). cbn [nth PbsrB0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { rewrite (BG.out_reg PbsrB0e.regs_out0 E' R' 26 Hregs) by (clear; lia). cbn [nth PbsrB0e.regs_out0]. first [reflexivity | wordP' ZA Hag]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 0); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 1); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 2); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 3); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 4); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 5); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 6); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 7); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 8); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 9); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 10); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 11); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 12); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 13); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 14); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1ma; [apply Hcells; apply (nth_error_In _ 15); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia | vm_compute; reflexivity]. }
  split. { eapply u8_of_KWord1a; [apply Hcells; apply (nth_error_In _ 16); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | byte_tac ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 17); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 18); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 19); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 20); reflexivity | evalEk' ZA Hag ltac:(clear - HV50l HV50r K3l K3r K13 K34 K35 K43) | evalEk' ZA Hag ltac:(clear - HV37l HV37r K7l K7r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 21); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk' ZA Hag ltac:(clear - HV34l HV34r) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 22); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 23); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply u64_of_KWord8a; [apply Hcells; apply (nth_error_In _ 24); reflexivity | evalEk' ZA Hag ltac:(clear - HV36l HV36r K8l K8r K10 K13 K31 K32 K33 K42) | evalEk' ZA Hag ltac:(clear - HV35l HV35r) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 25); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  split. { eapply defined_of_KUnka; [apply Hcells; apply (nth_error_In _ 26); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia]. }
  eapply zeros_of_KZeroa; [apply Hcells; apply (nth_error_In _ 27); reflexivity | evalEk' ZA Hag ltac:(clear - HV47l HV47r K19l K19r K23 K30 K31 K33 K34 K36 K53 K55 K56 K57) | evalEk' ZA Hag ltac:(clear) | clear; lia].
Qed.

End PMBSRP1.
